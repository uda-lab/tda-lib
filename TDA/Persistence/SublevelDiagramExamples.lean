import TDA.Persistence.SublevelDiagram
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
universe u w
namespace TDA.Persistence.Examples
open TDA.Simplicial TDA.Filtration TDA.Persistence CategoryTheory

private def emptyFilter (V : Type u) (α : Type w) [LinearOrder α] :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) α where
  value := fun s => ((mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro τ σ _
    exact ((mem_bot_iff τ.val).mp τ.property).elim

private instance emptyFaces (V : Type u) :
    Fintype (TotalFace (⊥ : PreAbstractSimplicialComplex V)) := by
  letI : IsEmpty (TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
    ⟨fun s => ((mem_bot_iff s.val).mp s.property).elim⟩
  exact Fintype.ofIsEmpty

private theorem empty_values (V : Type u) (α : Type w) [LinearOrder α] :
    (emptyFilter V α).criticalValues.card = 0 := by
  rw [((emptyFilter V α).criticalValues_eq_empty_iff).2 rfl]
  rfl

private theorem empty_points (V : Type u) [LinearOrder V]
    (α : Type w) [LinearOrder α] (k : Type u) [Field k] (n : ℕ) :
    (dgm k (emptyFilter V α) n).points = 0 := by
  have hi : IsEmpty (Fin (emptyFilter V α).criticalValues.card) := by
    rw [empty_values]
    infer_instance
  letI := hi
  simp [dgm, gradeHomologyBarcode, rankBarcode, ofIndexBars]

private theorem empty_rank (V : Type u) [LinearOrder V]
    (α : Type w) [LinearOrder α] (k : Type u) [Field k]
    (n : ℕ) (r s : α) (hrs : r ≤ s) :
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k ((emptyFilter V α).sublevel_mono hrs) n).hom) = 0 := by
  rw [rank_sublevelHomologyMap k (emptyFilter V α) n r s hrs,
    empty_points]
  rfl

private theorem empty_rank_count (V : Type u) [LinearOrder V]
    (α : Type w) [LinearOrder α] (k : Type u) [Field k]
    (n : ℕ) (r s : α) (hrs : r ≤ s) :
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k ((emptyFilter V α).sublevel_mono hrs) n).hom) =
      (dgm k (emptyFilter V α) n).points.countP
        (fun p => p.1 ≤ r ∧ (s : WithTop α) < p.2) :=
  rank_sublevelHomologyMap k (emptyFilter V α) n r s hrs

private theorem empty_real_all_degrees (n : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        ((emptyFilter (Fin 2) ℝ).sublevel_mono (show (0 : ℝ) ≤ 1 by norm_num)) n).hom) = 0 :=
  empty_rank (Fin 2) ℝ (ZMod 2) n 0 1 (by norm_num)

private theorem empty_value_type_points (V : Type u) [LinearOrder V]
    (k : Type u) [Field k] (n : ℕ) :
    (dgm k (emptyFilter V Empty) n).points = 0 :=
  empty_points V Empty k n

private theorem grade_consumer {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
    (f : FilterFunction K α) (n : ℕ)
    (i j : Fin f.criticalValues.card) (hij : i ≤ j) :
    Module.finrank k (LinearMap.range
      (simplicialHomologyIncl k (f.gradeFiltration.monotone hij) n).hom) =
    (dgm k f n).points.countP
      (fun p => p.1 ≤ f.criticalValue i ∧
        (f.criticalValue j : WithTop α) < p.2) := by
  have transport {A B A' B' : PreAbstractSimplicialComplex V}
      (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') :
      Module.finrank k (LinearMap.range (simplicialHomologyIncl k h n).hom) =
        Module.finrank k (LinearMap.range (simplicialHomologyIncl k h' n).hom) := by
    subst A'
    subst B'
    rfl
  exact (transport (f.gradeFiltration_apply i) (f.gradeFiltration_apply j)
    (f.gradeFiltration.monotone hij)
    (f.sublevel_mono (f.criticalValue.monotone hij))).trans
      (rank_sublevelHomologyMap k f n (f.criticalValue i) (f.criticalValue j)
        (f.criticalValue.monotone hij))

private theorem iso_consumer {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
    (f : FilterFunction K α) (n : ℕ)
    (B : Multiset (FiniteInterval f.criticalValues.card))
    (e : simplicialHomologyPModule k f.gradeFiltration n ≅
      barcodeModule (k := k) B) :
    dgm k f n = ofIndexBars f.criticalValue f.criticalValue.strictMono B :=
  dgm_eq_ofIndexBars_of_iso k f n B e

private theorem finite_multiplicity_consumer {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
    (f : FilterFunction K α) (n : ℕ)
    (b d : Fin f.criticalValues.card) (hbd : b < d) :
    ((dgm k f n).points.count
      (f.criticalValue b, (f.criticalValue d : WithTop α)) : ℤ) =
      moduleMultiplicityInteger
        (simplicialHomologyPModule k f.gradeFiltration n) b.val d.val := by
  rw [dgm, ofIndexBars_count_finite]
  exact barcodeMultiplicity_rankBarcode
    (simplicialHomologyPModule k f.gradeFiltration n)
    b.val d.val hbd (Nat.le_of_lt d.isLt)

private theorem essential_multiplicity_consumer {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
    (f : FilterFunction K α) (n : ℕ)
    (b : Fin f.criticalValues.card) :
    ((dgm k f n).points.count
      (f.criticalValue b, (⊤ : WithTop α)) : ℤ) =
      moduleMultiplicityInteger
        (simplicialHomologyPModule k f.gradeFiltration n)
        b.val f.criticalValues.card := by
  rw [dgm, ofIndexBars_count_essential]
  exact barcodeMultiplicity_rankBarcode
    (simplicialHomologyPModule k f.gradeFiltration n)
    b.val f.criticalValues.card b.isLt le_rfl

private theorem diagonal_zero_consumer {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
    (f : FilterFunction K α) (n : ℕ)
    (b : Fin f.criticalValues.card) :
    (dgm k f n).points.count
      (f.criticalValue b, (f.criticalValue b : WithTop α)) = 0 := by
  rw [dgm, ofIndexBars_count_finite]
  apply Multiset.countP_eq_zero.mpr
  intro I _ h
  exact (ne_of_lt I.birth_lt_death) (h.1.trans h.2.symm)

private theorem empty_iso_consumer (V : Type u) [LinearOrder V]
    (α : Type w) [LinearOrder α] (k : Type u) [Field k] (n : ℕ) :
    dgm k (emptyFilter V α) n =
      ofIndexBars (emptyFilter V α).criticalValue
        (emptyFilter V α).criticalValue.strictMono
        (0 : Multiset (FiniteInterval (emptyFilter V α).criticalValues.card)) := by
  have hi : IsEmpty (Fin (emptyFilter V α).criticalValues.card) := by
    rw [empty_values]
    infer_instance
  letI := hi
  have he : simplicialHomologyPModule k (emptyFilter V α).gradeFiltration n =
      barcodeModule (k := k)
        (0 : Multiset (FiniteInterval (emptyFilter V α).criticalValues.card)) := by
    apply CategoryTheory.Functor.ext
    · intro i
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i
  exact iso_consumer k (emptyFilter V α) n 0 (eqToIso he)

private theorem reversed_zero_consumer {V : Type u} [LinearOrder V]
    (k : Type u) [Field k] {α : Type w} [LinearOrder α]
    {K : PreAbstractSimplicialComplex V} [Fintype (TotalFace K)]
    (f : FilterFunction K α) (n : ℕ)
    (b d : Fin f.criticalValues.card) (hdb : d < b) :
    (dgm k f n).points.count
      (f.criticalValue b, (f.criticalValue d : WithTop α)) = 0 := by
  rw [dgm, ofIndexBars_count_finite]
  apply Multiset.countP_eq_zero.mpr
  intro I _ h
  have hbd := I.birth_lt_death
  rw [h.1, h.2] at hbd
  exact (not_lt_of_ge (Nat.le_of_lt hdb)) hbd

private instance singletonMem (s : Finset (Fin 2)) :
    Decidable (s ∈ singletonFace (0 : Fin 2)) :=
  decidable_of_iff (s = {0}) (mem_singletonFace_iff 0 s).symm

private instance singletonFaces : Fintype (TotalFace (singletonFace (0 : Fin 2))) :=
  inferInstance

private def singletonFilter (a : ℝ) : FilterFunction (singletonFace (0 : Fin 2)) ℝ where
  value := fun _ => a
  mono := by intros; exact le_rfl

private theorem singleton_values (a : ℝ) :
    (singletonFilter a).criticalValues = {a} := by
  ext b
  constructor
  · intro hb
    obtain ⟨σ, hσ⟩ := ((singletonFilter a).mem_criticalValues b).1 hb
    exact Finset.mem_singleton.mpr (by simpa [singletonFilter] using hσ.symm)
  · intro hb
    have hface : ({0} : Finset (Fin 2)) ∈ singletonFace (0 : Fin 2) := by
      exact (mem_singletonFace_iff _ _).2 rfl
    have hb' : b = a := Finset.mem_singleton.mp hb
    subst b
    exact ((singletonFilter a).mem_criticalValues a).2 ⟨⟨{0}, hface⟩, rfl⟩

private theorem singleton_card (a : ℝ) :
    (singletonFilter a).criticalValues.card = 1 := by
  rw [singleton_values]
  simp

private noncomputable def singleton_i (a : ℝ) : Fin (singletonFilter a).criticalValues.card :=
  ⟨0, by rw [singleton_card]; decide⟩

private theorem singleton_critical (a : ℝ) :
    (singletonFilter a).criticalValue (singleton_i a) = a := by
  have h := (singletonFilter a).criticalValue_mem (singleton_i a)
  simpa [singleton_values] using h

private theorem singleton_stage (a : ℝ) :
    (singletonFilter a).gradeFiltration (singleton_i a) = singletonFace (0 : Fin 2) := by
  rw [(singletonFilter a).gradeFiltration_apply, singleton_critical]
  apply (singletonFilter a).sublevel_eq_self_of_forall_le
  intro s
  rfl

private theorem singleton_h0 (a : ℝ) :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2)
        (singletonFilter a).gradeFiltration 0).obj (singleton_i a)) = 1 := by
  rw [simplicialHomologyPModule_obj, singleton_stage]
  exact (simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
    (Module.finrank_self (ZMod 2))

private noncomputable def singleton_bar (a : ℝ) :
    FiniteInterval (singletonFilter a).criticalValues.card :=
  ⟨0, 1, by omega, by rw [singleton_card]⟩

private theorem singleton_barcode (a : ℝ) :
    gradeHomologyBarcode (ZMod 2) (singletonFilter a) 0 =
      ({singleton_bar a} :
        Multiset (FiniteInterval (singletonFilter a).criticalValues.card)) := by
  calc
    gradeHomologyBarcode (ZMod 2) (singletonFilter a) 0 =
        rankBarcode (barcodeModule (k := ZMod 2)
          ({singleton_bar a} :
            Multiset (FiniteInterval (singletonFilter a).criticalValues.card))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule (ZMod 2) (singletonFilter a).gradeFiltration 0)
        (barcodeModule (k := ZMod 2)
          ({singleton_bar a} :
            Multiset (FiniteInterval (singletonFilter a).criticalValues.card)))).mpr
      intro i j hij
      have hi : i = singleton_i a := by
        apply Fin.ext
        have hh := i.isLt
        have hc := singleton_card a
        omega
      have hj : j = singleton_i a := by
        apply Fin.ext
        have hh := j.isLt
        have hc := singleton_card a
        omega
      subst i
      subst j
      rw [rank_barcodeMap]
      have hr : structureMapRank
          (simplicialHomologyPModule (ZMod 2) (singletonFilter a).gradeFiltration 0)
          (singleton_i a) (singleton_i a) hij = 1 := by
        unfold structureMapRank
        rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
        exact singleton_h0 a
      rw [hr]
      rw [show ({singleton_bar a} :
        Multiset (FiniteInterval (singletonFilter a).criticalValues.card)) =
          singleton_bar a ::ₘ 0 by rfl, Multiset.countP_cons]
      simp [singleton_bar, singleton_i]
    _ = _ := rankBarcode_barcodeModule _

private theorem singleton_points (a : ℝ) :
    (dgm (ZMod 2) (singletonFilter a) 0).points =
      ({(a, (⊤ : WithTop ℝ))} : Multiset (ℝ × WithTop ℝ)) := by
  rw [dgm, singleton_barcode]
  simp [ofIndexBars, singleton_bar]
  change ((singletonFilter a).criticalValue (singleton_i a),
      if hd : 1 < (singletonFilter a).criticalValues.card then
        ((singletonFilter a).criticalValue ⟨1, hd⟩ : WithTop ℝ)
      else (⊤ : WithTop ℝ)) = (a, ⊤)
  simp [singleton_card, singleton_critical]

private theorem singleton_below (a r : ℝ) (hr : r < a) :
    (singletonFilter a).sublevel r = ⊥ := by
  apply (singletonFilter a).sublevel_eq_bot_of_forall_lt
  intro σ
  simpa [singletonFilter] using hr

private theorem singleton_tail (a r : ℝ) (hr : a ≤ r) :
    (singletonFilter a).sublevel r = singletonFace (0 : Fin 2) := by
  apply (singletonFilter a).sublevel_eq_self_of_forall_le
  intro σ
  simpa [singletonFilter] using hr

private theorem same_complex_identity
    {A B C : PreAbstractSimplicialComplex (Fin 2)}
    (hA : A = C) (hB : B = C) (h : A ≤ B) :
    simplicialHomologyIncl (ZMod 2) h 0 ≫
      eqToHom (congrArg (fun D => simplicialHomology D (ZMod 2) 0) hB) =
      eqToHom (congrArg (fun D => simplicialHomology D (ZMod 2) 0) hA) := by
  subst A
  subst B
  simp [simplicialHomologyIncl_id]

private theorem singleton_tail_identity (a r s : ℝ) (har : a ≤ r) (hrs : r ≤ s) :
    simplicialHomologyIncl (ZMod 2)
        ((singletonFilter a).sublevel_mono hrs) 0 ≫
      eqToHom (congrArg
        (fun C => simplicialHomology C (ZMod 2) 0)
        (singleton_tail a s (har.trans hrs))) =
      eqToHom (congrArg
        (fun C => simplicialHomology C (ZMod 2) 0)
        (singleton_tail a r har)) := by
  exact same_complex_identity (singleton_tail a r har)
    (singleton_tail a s (har.trans hrs)) _

private theorem singleton_below_rank (a r s : ℝ) (hr : r < a) (hrs : r ≤ s) :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        ((singletonFilter a).sublevel_mono hrs) 0).hom) = 0 := by
  rw [rank_sublevelHomologyMap (ZMod 2) (singletonFilter a) 0 r s hrs,
    singleton_points]
  rw [show ({(a, (⊤ : WithTop ℝ))} : Multiset (ℝ × WithTop ℝ)) =
    (a, ⊤) ::ₘ 0 by rfl, Multiset.countP_cons]
  simp [not_le.mpr hr]

private theorem singleton_tail_rank (a r s : ℝ) (har : a ≤ r) (hrs : r ≤ s) :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        ((singletonFilter a).sublevel_mono hrs) 0).hom) = 1 ∧
    (dgm (ZMod 2) (singletonFilter a) 0).points.countP
      (fun p => p.1 ≤ r ∧ (s : WithTop ℝ) < p.2) = 1 := by
  have hc : (dgm (ZMod 2) (singletonFilter a) 0).points.countP
      (fun p => p.1 ≤ r ∧ (s : WithTop ℝ) < p.2) = 1 := by
    rw [singleton_points]
    rw [show ({(a, (⊤ : WithTop ℝ))} : Multiset (ℝ × WithTop ℝ)) =
      (a, ⊤) ::ₘ 0 by rfl, Multiset.countP_cons]
    simp [har]
  exact ⟨(rank_sublevelHomologyMap (ZMod 2) (singletonFilter a) 0
    r s hrs).trans hc, hc⟩

private theorem singleton_self_rank (a : ℝ) :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        ((singletonFilter a).sublevel_mono (le_refl a)) 0).hom) = 1 :=
  (singleton_tail_rank a a a le_rfl le_rfl).1

private theorem singleton_gap_tail (a : ℝ) :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        ((singletonFilter a).sublevel_mono (show a + 1 ≤ a + 2 by linarith)) 0).hom) =
      1 :=
  (singleton_tail_rank a (a + 1) (a + 2) (by linarith) (by linarith)).1

private theorem singleton_diagonal_absent (a : ℝ) :
    (dgm (ZMod 2) (singletonFilter a) 0).points.count
      (a, (a : WithTop ℝ)) = 0 := by
  rw [singleton_points]
  simp

private abbrev edgeK : PreAbstractSimplicialComplex (Fin 2) := ⊤

private instance edgeMem (s : Finset (Fin 2)) : Decidable (s ∈ edgeK) := by
  change Decidable s.Nonempty
  infer_instance

private instance edgeFaces : Fintype (TotalFace edgeK) := inferInstance

private theorem edge_face_cases (s : TotalFace edgeK) :
    s.val = ({0} : Finset (Fin 2)) ∨
    s.val = ({1} : Finset (Fin 2)) ∨
    s.val = ({0, 1} : Finset (Fin 2)) := by
  have h : ∀ t : Finset (Fin 2), t.Nonempty →
      t = ({0} : Finset (Fin 2)) ∨ t = ({1} : Finset (Fin 2)) ∨
      t = ({0, 1} : Finset (Fin 2)) := by decide
  exact h s.val s.property

private def edgeFilter : FilterFunction edgeK ℝ where
  value := fun s =>
    if s.val = ({0} : Finset (Fin 2)) then 2
    else if s.val = ({1} : Finset (Fin 2)) then 5
    else 9
  mono := by
    intro τ σ hsub
    rcases edge_face_cases τ with hτ | hτ | hτ <;>
      rcases edge_face_cases σ with hσ | hσ | hσ <;>
      simp [hτ, hσ, Finset.subset_iff] at hsub ⊢
    all_goals norm_num [Finset.ext_iff] at *

private def edge_v0 : TotalFace edgeK := ⟨{0}, by decide⟩
private def edge_v1 : TotalFace edgeK := ⟨{1}, by decide⟩
private def edge_e01 : TotalFace edgeK := ⟨{0, 1}, by decide⟩

private theorem edge_values :
    edgeFilter.value edge_v0 = 2 ∧
    edgeFilter.value edge_v1 = 5 ∧
    edgeFilter.value edge_e01 = 9 := by
  norm_num [edgeFilter, edge_v0, edge_v1, edge_e01, Finset.ext_iff]

private theorem edge_critical_set :
    edgeFilter.criticalValues = ({2, 5, 9} : Finset ℝ) := by
  ext b
  constructor
  · intro hb
    obtain ⟨σ, hσ⟩ := (edgeFilter.mem_criticalValues b).1 hb
    rcases edge_face_cases σ with h | h | h <;>
      simp [edgeFilter, h, Finset.ext_iff] at hσ ⊢
    all_goals subst b <;> simp_all
  · intro hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact (edgeFilter.mem_criticalValues 2).2 ⟨edge_v0, edge_values.1⟩
    · exact (edgeFilter.mem_criticalValues 5).2 ⟨edge_v1, edge_values.2.1⟩
    · exact (edgeFilter.mem_criticalValues 9).2 ⟨edge_e01, edge_values.2.2⟩

private theorem edge_card : edgeFilter.criticalValues.card = 3 := by
  rw [edge_critical_set]
  norm_num

private noncomputable def edge_i0 : Fin edgeFilter.criticalValues.card :=
  ⟨0, by rw [edge_card]; decide⟩
private noncomputable def edge_i1 : Fin edgeFilter.criticalValues.card :=
  ⟨1, by rw [edge_card]; decide⟩
private noncomputable def edge_i2 : Fin edgeFilter.criticalValues.card :=
  ⟨2, by rw [edge_card]; decide⟩

private theorem edge_critical :
    edgeFilter.criticalValue edge_i0 = 2 ∧
    edgeFilter.criticalValue edge_i1 = 5 ∧
    edgeFilter.criticalValue edge_i2 = 9 := by
  have h0 := edgeFilter.criticalValue_mem edge_i0
  have h1 := edgeFilter.criticalValue_mem edge_i1
  have h2 := edgeFilter.criticalValue_mem edge_i2
  have h01 : edgeFilter.criticalValue edge_i0 < edgeFilter.criticalValue edge_i1 :=
    edgeFilter.criticalValue.strictMono (by apply Fin.lt_def.mpr; decide)
  have h12 : edgeFilter.criticalValue edge_i1 < edgeFilter.criticalValue edge_i2 :=
    edgeFilter.criticalValue.strictMono (by apply Fin.lt_def.mpr; decide)
  simp only [edge_critical_set, Finset.mem_insert, Finset.mem_singleton] at h0 h1 h2
  rcases h0 with h0 | h0 | h0 <;>
    rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    simp_all <;> linarith

private theorem edge_mem_sublevel (r : ℝ) (s : Finset (Fin 2)) :
    s ∈ edgeFilter.sublevel r ↔
      (s = {0} ∧ (2 : ℝ) ≤ r) ∨
      (s = {1} ∧ (5 : ℝ) ≤ r) ∨
      (s = {0, 1} ∧ (9 : ℝ) ≤ r) := by
  constructor
  · intro hs
    obtain ⟨hsK, hv⟩ := (edgeFilter.mem_sublevel_iff r s).1 hs
    rcases edge_face_cases (⟨s, hsK⟩ : TotalFace edgeK) with h | h | h
    · left
      refine ⟨h, ?_⟩
      have hs : (⟨s, hsK⟩ : TotalFace edgeK) = edge_v0 := Subtype.ext h
      rw [hs, edge_values.1] at hv
      exact hv
    · right; left
      refine ⟨h, ?_⟩
      have hs : (⟨s, hsK⟩ : TotalFace edgeK) = edge_v1 := Subtype.ext h
      rw [hs, edge_values.2.1] at hv
      exact hv
    · right; right
      refine ⟨h, ?_⟩
      have hs : (⟨s, hsK⟩ : TotalFace edgeK) = edge_e01 := Subtype.ext h
      rw [hs, edge_values.2.2] at hv
      exact hv
  · rintro (⟨rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨rfl, hr⟩)
    · exact (edgeFilter.mem_sublevel_iff r _).2
        ⟨edge_v0.property, by simpa [edgeFilter, edge_v0] using hr⟩
    · exact (edgeFilter.mem_sublevel_iff r _).2
        ⟨edge_v1.property, by simpa [edgeFilter, edge_v1, Finset.ext_iff] using hr⟩
    · exact (edgeFilter.mem_sublevel_iff r _).2
        ⟨edge_e01.property, by simpa [edgeFilter, edge_e01, Finset.ext_iff] using hr⟩

private abbrev edge_twoVertices : PreAbstractSimplicialComplex (Fin 2) :=
  singletonFace (0 : Fin 2) ⊔ singletonFace (1 : Fin 2)

private theorem edge_below (r : ℝ) (hr : r < 2) :
    edgeFilter.sublevel r = ⊥ := by
  apply edgeFilter.sublevel_eq_bot_of_lt_first (by rw [edge_card]; decide) r
  change r < edgeFilter.criticalValue edge_i0
  rw [edge_critical.1]
  exact hr

private theorem edge_region0 (r : ℝ) (hlo : (2 : ℝ) ≤ r) (hhi : r < 5) :
    edgeFilter.sublevel r = singletonFace (0 : Fin 2) := by
  ext s
  change s ∈ edgeFilter.sublevel r ↔ s ∈ singletonFace (0 : Fin 2)
  rw [edge_mem_sublevel]
  have h9 : ¬ (9 : ℝ) ≤ r := by linarith
  simp [mem_singletonFace_iff, hlo, not_le.mpr hhi, h9]

private theorem edge_region1 (r : ℝ) (hlo : (5 : ℝ) ≤ r) (hhi : r < 9) :
    edgeFilter.sublevel r = edge_twoVertices := by
  ext s
  change s ∈ edgeFilter.sublevel r ↔ s ∈ edge_twoVertices
  rw [edge_mem_sublevel]
  have h2 : (2 : ℝ) ≤ r := by linarith
  have h9 : ¬ (9 : ℝ) ≤ r := by linarith
  simp only [h2, hlo, h9, and_true, and_false, or_false]
  change (s = {0} ∨ s = {1}) ↔ (s = {0} ∨ s = {1})
  rfl

private theorem edge_region2 (r : ℝ) (hlo : (9 : ℝ) ≤ r) :
    edgeFilter.sublevel r = edgeK := by
  apply edgeFilter.sublevel_eq_self_of_last_le
    (by rw [edge_card]; decide) r
  have hlast : (⟨edgeFilter.criticalValues.card - 1,
      Nat.sub_lt (show 0 < edgeFilter.criticalValues.card by rw [edge_card]; decide)
        (by decide)⟩ : Fin edgeFilter.criticalValues.card) = edge_i2 := by
    apply Fin.ext
    change edgeFilter.criticalValues.card - 1 = 2
    have hc := edge_card
    omega
  rw [hlast, edge_critical.2.2]
  exact hlo

private theorem edge_stage0 : edgeFilter.gradeFiltration edge_i0 =
    singletonFace (0 : Fin 2) := by
  rw [edgeFilter.gradeFiltration_apply, edge_critical.1]
  exact edge_region0 2 le_rfl (by norm_num)

private theorem edge_stage1 : edgeFilter.gradeFiltration edge_i1 = edge_twoVertices := by
  rw [edgeFilter.gradeFiltration_apply, edge_critical.2.1]
  exact edge_region1 5 le_rfl (by norm_num)

private theorem edge_stage2 : edgeFilter.gradeFiltration edge_i2 = edgeK := by
  rw [edgeFilter.gradeFiltration_apply, edge_critical.2.2]
  exact edge_region2 9 le_rfl

private instance edgeTwoMem (s : Finset (Fin 2)) : Decidable (s ∈ edge_twoVertices) := by
  change Decidable (s = {0} ∨ s = {1})
  infer_instance

private instance edgeTwoFaces : Fintype (TotalFace edge_twoVertices) := inferInstance

private instance edgeTwoNoEdges : IsEmpty (Face edge_twoVertices 1) :=
  ⟨fun σ => by
    have hs : σ.1 = ({0} : Finset (Fin 2)) ∨ σ.1 = {1} := σ.2.1
    have hc := σ.2.2
    rcases hs with h | h <;> simp [h] at hc⟩

private theorem edgeTwo_face0_card : Fintype.card (Face edge_twoVertices 0) = 2 := by
  decide

private theorem edgeTwo_short_f_zero :
    ((simplicialChainComplex edge_twoVertices (ZMod 2)).sc 0).f = 0 := by
  have hf : (simplicialChainComplex edge_twoVertices (ZMod 2)).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change (boundary edge_twoVertices (ZMod 2) 0) c = 0
    have hc : c = 0 := by
      change Chain edge_twoVertices (ZMod 2) 1 at c
      exact Subsingleton.elim c 0
    rw [hc]
    exact map_zero _
  change (simplicialChainComplex edge_twoVertices (ZMod 2)).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

private theorem edgeTwo_short_g_zero :
    ((simplicialChainComplex edge_twoVertices (ZMod 2)).sc 0).g = 0 := by
  change (simplicialChainComplex edge_twoVertices (ZMod 2)).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero edge_twoVertices (ZMod 2) 0

private noncomputable abbrev edgeTwoShort :=
  (simplicialChainComplex edge_twoVertices (ZMod 2)).sc 0

private noncomputable def edgeTwoH0Equiv :
    simplicialHomology edge_twoVertices (ZMod 2) 0 ≃ₗ[ZMod 2]
      Chain edge_twoVertices (ZMod 2) 0 :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((simplicialChainComplex edge_twoVertices (ZMod 2)).sc 0)
    edgeTwo_short_f_zero edgeTwo_short_g_zero).homologyIso.toLinearEquiv

private theorem edgeTwo_zeroBoundaryNormalization :
    edgeTwoShort.moduleCatLeftHomologyData.π ≫
        edgeTwoShort.moduleCatHomologyIso.inv ≫
        (ShortComplex.LeftHomologyData.ofZeros edgeTwoShort
          edgeTwo_short_f_zero edgeTwo_short_g_zero).homologyIso.hom =
      edgeTwoShort.moduleCatLeftHomologyData.i := by
  let S := edgeTwoShort
  change S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv ≫
    (ShortComplex.LeftHomologyData.ofZeros S
      edgeTwo_short_f_zero edgeTwo_short_g_zero).homologyIso.hom =
      S.moduleCatLeftHomologyData.i
  rw [← Category.assoc, ← S.moduleCatCyclesIso_inv_π]
  rw [Category.assoc,
    (ShortComplex.LeftHomologyData.ofZeros S
      edgeTwo_short_f_zero edgeTwo_short_g_zero).homologyπ_comp_homologyIso_hom]
  simp only [ShortComplex.LeftHomologyData.ofZeros_π]
  have hci : (ShortComplex.LeftHomologyData.ofZeros S
      edgeTwo_short_f_zero edgeTwo_short_g_zero).cyclesIso.hom =
      S.iCycles := by
    simpa [ShortComplex.LeftHomologyData.ofZeros] using
      (ShortComplex.LeftHomologyData.ofZeros S
        edgeTwo_short_f_zero edgeTwo_short_g_zero).cyclesIso_hom_comp_i
  rw [hci]
  exact S.moduleCatCyclesIso_inv_iCycles

private theorem edgeOne_short_f_zero :
    ((simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)).sc 0).f = 0 := by
  have hf : (simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change boundary (singletonFace (0 : Fin 2)) (ZMod 2) 0 c = 0
    have hc := singletonHigherChain_eq_zero (0 : Fin 2) (ZMod 2) 0 c
    rw [hc]
    simp
  change (simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

private theorem edgeOne_short_g_zero :
    ((simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)).sc 0).g = 0 := by
  change (simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero _ (ZMod 2) 0

private noncomputable def edgeOneH0Equiv :
    simplicialHomology (singletonFace (0 : Fin 2)) (ZMod 2) 0 ≃ₗ[ZMod 2]
      Chain (singletonFace (0 : Fin 2)) (ZMod 2) 0 :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)).sc 0)
    edgeOne_short_f_zero edgeOne_short_g_zero).homologyIso.toLinearEquiv

private theorem edgeOther_short_f_zero :
    ((simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)).sc 0).f = 0 := by
  have hf : (simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)).d 1 0 = 0 := by
    apply ModuleCat.hom_ext
    ext c
    change boundary (singletonFace (1 : Fin 2)) (ZMod 2) 0 c = 0
    have hc := singletonHigherChain_eq_zero (1 : Fin 2) (ZMod 2) 0 c
    rw [hc]
    simp
  change (simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)).d
    ((ComplexShape.down ℕ).prev 0) 0 = 0
  rw [ChainComplex.prev]
  exact hf

private theorem edgeOther_short_g_zero :
    ((simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)).sc 0).g = 0 := by
  change (simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)).d
    0 ((ComplexShape.down ℕ).next 0) = 0
  rw [ChainComplex.next_nat_zero]
  exact simplicialChainComplex_d_zero _ (ZMod 2) 0

private noncomputable def edgeOtherH0Equiv :
    simplicialHomology (singletonFace (1 : Fin 2)) (ZMod 2) 0 ≃ₗ[ZMod 2]
      Chain (singletonFace (1 : Fin 2)) (ZMod 2) 0 :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)).sc 0)
    edgeOther_short_f_zero edgeOther_short_g_zero).homologyIso.toLinearEquiv

private def edge_twoVertex (i : Fin 2) : Face edge_twoVertices 0 :=
  ⟨{i}, by
    fin_cases i
    · change ({0} : Finset (Fin 2)) = {0} ∨ ({0} : Finset (Fin 2)) = {1}
      exact Or.inl rfl
    · change ({1} : Finset (Fin 2)) = {0} ∨ ({1} : Finset (Fin 2)) = {1}
      exact Or.inr rfl, by simp⟩

private theorem edge_twoVertex_bijective : Function.Bijective edge_twoVertex := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> first | rfl | simp [edge_twoVertex] at hv
  · intro σ
    have hc : σ.1 = {(0 : Fin 2)} ∨ σ.1 = {(1 : Fin 2)} := by
      have h : ∀ t : Finset (Fin 2), t.card = 1 →
          t = {0} ∨ t = {1} := by decide
      exact h σ.1 σ.2.2
    rcases hc with hc | hc
    · exact ⟨0, Subtype.ext (by simpa [edge_twoVertex] using hc.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [edge_twoVertex] using hc.symm)⟩

private theorem edge_twoVertex_ne : edge_twoVertex 0 ≠ edge_twoVertex 1 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [edge_twoVertex] at hv

private noncomputable def edgeTwoPairEquiv :
    simplicialHomology edge_twoVertices (ZMod 2) 0 ≃ₗ[ZMod 2]
      ZMod 2 × ZMod 2 :=
  (edgeTwoH0Equiv.trans
    (Finsupp.mapDomain.linearEquiv (M := ZMod 2) (R := ZMod 2)
      (Equiv.ofBijective edge_twoVertex edge_twoVertex_bijective).symm)).trans
    ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin 2)).trans
      (LinearEquiv.finTwoArrow (R := ZMod 2) (M := ZMod 2)))

private theorem edgeTwoPairEquiv_apply
    (x : simplicialHomology edge_twoVertices (ZMod 2) 0) :
    edgeTwoPairEquiv x =
      ((edgeTwoH0Equiv x) (edge_twoVertex 0),
       (edgeTwoH0Equiv x) (edge_twoVertex 1)) := by
  simp [edgeTwoPairEquiv, Finsupp.mapDomain.linearEquiv]

private theorem edge_H0_stage0 :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2) edgeFilter.gradeFiltration 0).obj edge_i0) = 1 := by
  rw [simplicialHomologyPModule_obj, edge_stage0]
  exact (simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
    (Module.finrank_self (ZMod 2))

private theorem edge_H0_stage1 :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2) edgeFilter.gradeFiltration 0).obj edge_i1) = 2 := by
  rw [simplicialHomologyPModule_obj, edge_stage1]
  rw [edgeTwoH0Equiv.finrank_eq]
  change Module.finrank (ZMod 2) (Chain edge_twoVertices (ZMod 2) 0) = 2
  rw [Module.finrank_finsupp_self]
  exact edgeTwo_face0_card

private def edge_vertex (i : Fin 2) : Face edgeK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 2)).Nonempty; simp, by simp⟩

private def edge_face : Face edgeK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 2)).Nonempty; decide, by decide⟩

private theorem edge_vertex_bijective : Function.Bijective edge_vertex := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> first | rfl | simp [edge_vertex] at hv
  · intro σ
    have hc : σ.1 = {(0 : Fin 2)} ∨ σ.1 = {(1 : Fin 2)} := by
      have h : ∀ t : Finset (Fin 2), t.card = 1 →
          t = {0} ∨ t = {1} := by decide
      exact h σ.1 σ.2.2
    rcases hc with hc | hc
    · exact ⟨0, Subtype.ext (by simpa [edge_vertex] using hc.symm)⟩
    · exact ⟨1, Subtype.ext (by simpa [edge_vertex] using hc.symm)⟩

private theorem edge_face_unique (σ : Face edgeK 1) : σ = edge_face := by
  apply Subtype.ext
  have h : ∀ t : Finset (Fin 2), t.card = 2 → t = {0, 1} := by decide
  exact h σ.1 σ.2.2

private theorem edge_face_orderEmb :
    edge_face.1.orderEmbOfFin edge_face.2.2 =
      Fin.castLEOrderEmb (by decide : 2 ≤ 2) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  fin_cases i <;> simp [edge_face]

private theorem edge_deleted0 : deletedFace edgeK 0 edge_face 0 = edge_vertex 1 := by
  apply Subtype.ext
  change edge_face.1.erase (edge_face.1.orderEmbOfFin edge_face.2.2 0) =
    (edge_vertex 1).1
  rw [edge_face_orderEmb]
  decide

private theorem edge_deleted1 : deletedFace edgeK 0 edge_face 1 = edge_vertex 0 := by
  apply Subtype.ext
  change edge_face.1.erase (edge_face.1.orderEmbOfFin edge_face.2.2 1) =
    (edge_vertex 0).1
  rw [edge_face_orderEmb]
  decide

private theorem edge_boundary (a : ZMod 2) :
    boundary edgeK (ZMod 2) 0 (Finsupp.single edge_face a) =
      Finsupp.single (edge_vertex 1) a - Finsupp.single (edge_vertex 0) a := by
  rw [boundary_single]
  simp only [Fin.sum_univ_succ, edge_deleted0]
  have hdel : deletedFace edgeK 0 edge_face (Fin.succ 0) = edge_vertex 0 := by
    simpa using edge_deleted1
  rw [hdel]
  norm_num
  rw [sub_eq_add_neg]

private theorem edge_vertex_ne : edge_vertex 0 ≠ edge_vertex 1 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [edge_vertex] at hv

private theorem edge_face0_card : Fintype.card (Face edgeK 0) = 2 := by
  exact Fintype.card_congr (Equiv.ofBijective edge_vertex edge_vertex_bijective).symm

private theorem edge_face1_card : Fintype.card (Face edgeK 1) = 1 := by
  decide

private theorem edge_chain0_finrank :
    Module.finrank (ZMod 2) (Chain edgeK (ZMod 2) 0) = 2 := by
  rw [Module.finrank_finsupp_self]
  exact edge_face0_card

private theorem edge_chain1_finrank :
    Module.finrank (ZMod 2) (Chain edgeK (ZMod 2) 1) = 1 := by
  rw [Module.finrank_finsupp_self]
  exact edge_face1_card

private theorem edge_boundary_nonzero :
    boundary edgeK (ZMod 2) 0 (Finsupp.single edge_face 1) ≠ 0 := by
  intro h
  have hc := congrArg (fun c : Chain edgeK (ZMod 2) 0 => c (edge_vertex 1)) h
  rw [edge_boundary] at hc
  simp [edge_vertex_ne.symm] at hc

private theorem edge_boundaries_finrank :
    Module.finrank (ZMod 2) (simplicialBoundaries edgeK (ZMod 2) 0) = 1 := by
  let S := (simplicialChainComplex edgeK (ZMod 2)).sc 0
  letI : FiniteDimensional (ZMod 2) (↑S.X₁) := by
    change FiniteDimensional (ZMod 2)
      (Chain edgeK (ZMod 2) ((ComplexShape.down ℕ).prev 0))
    rw [ChainComplex.prev]
    exact finiteDimensional_finsupp
  letI : FiniteDimensional (ZMod 2) (LinearMap.range S.moduleCatToCycles) :=
    inferInstance
  have hpos : 0 < Module.finrank (ZMod 2)
      (LinearMap.range S.moduleCatToCycles) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let z : simplicialCycles edgeK (ZMod 2) 0 :=
      ⟨boundary edgeK (ZMod 2) 0 (Finsupp.single edge_face 1), by
        rw [simplicialCycles_zero]; trivial⟩
    have hz : z ∈ simplicialBoundaries edgeK (ZMod 2) 0 :=
      (mem_simplicialBoundaries_iff (ZMod 2) edgeK 0 z).2
        ⟨Finsupp.single edge_face 1, rfl⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    intro hz
    have hc : z = 0 := congrArg Subtype.val hz
    apply edge_boundary_nonzero
    exact congrArg (fun t : simplicialCycles edgeK (ZMod 2) 0 =>
      (t : Chain edgeK (ZMod 2) 0)) hc
  have hle := LinearMap.finrank_range_le S.moduleCatToCycles
  have hdim := edge_chain1_finrank
  have hsource : Module.finrank (ZMod 2) (↑S.X₁) = 1 := by
    change Module.finrank (ZMod 2)
      (Chain edgeK (ZMod 2) ((ComplexShape.down ℕ).prev 0)) = 1
    rw [ChainComplex.prev]
    exact hdim
  rw [hsource] at hle
  change Module.finrank (ZMod 2) (LinearMap.range S.moduleCatToCycles) = 1
  omega

private theorem edge_H0_stage2 :
    Module.finrank (ZMod 2)
      ((simplicialHomologyPModule (ZMod 2) edgeFilter.gradeFiltration 0).obj edge_i2) = 1 := by
  rw [simplicialHomologyPModule_obj, edge_stage2]
  letI : Finite (Face edgeK 0) := inferInstance
  letI : FiniteDimensional (ZMod 2) (Chain edgeK (ZMod 2) 0) :=
    finiteDimensional_finsupp
  letI : FiniteDimensional (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0) :=
    inferInstance
  letI : HasQuotient (simplicialCycles edgeK (ZMod 2) 0)
      (Submodule (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2) (M := simplicialCycles edgeK (ZMod 2) 0)
  change Module.finrank (ZMod 2)
    ((simplicialChainComplex edgeK (ZMod 2)).homology 0) = 1
  rw [(homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv.finrank_eq]
  change Module.finrank (ZMod 2)
    (simplicialCycles edgeK (ZMod 2) 0 ⧸ simplicialBoundaries edgeK (ZMod 2) 0) = 1
  have hq : Module.finrank (ZMod 2)
      (simplicialCycles edgeK (ZMod 2) 0 ⧸ simplicialBoundaries edgeK (ZMod 2) 0) +
      Module.finrank (ZMod 2) (simplicialBoundaries edgeK (ZMod 2) 0) =
      Module.finrank (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0) := by
    exact Submodule.finrank_quotient_add_finrank _
  have hc : Module.finrank (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0) = 2 := by
    rw [simplicialCycles_zero, finrank_top]
    exact edge_chain0_finrank
  have hb := edge_boundaries_finrank
  omega

private noncomputable def edge_coeffSum :
    Chain edgeK (ZMod 2) 0 →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.lsum (ZMod 2) (fun _ => LinearMap.id)

private noncomputable def edgeTwo_coeffSum :
    Chain edge_twoVertices (ZMod 2) 0 →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.lsum (ZMod 2) (fun _ => LinearMap.id)

private theorem edgeTwo_coeffSum_coords
    (c : Chain edge_twoVertices (ZMod 2) 0) :
    edgeTwo_coeffSum c = c (edge_twoVertex 0) + c (edge_twoVertex 1) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, Finsupp.add_apply, hc, hd, add_add_add_comm]
  | single v a =>
      obtain ⟨i, rfl⟩ := edge_twoVertex_bijective.2 v
      fin_cases i
      · simp [edgeTwo_coeffSum, edge_twoVertex_ne]
      · simp [edgeTwo_coeffSum, edge_twoVertex_ne.symm]

private theorem edge_coeffSum_single (i : Fin 2) (a : ZMod 2) :
    edge_coeffSum (Finsupp.single (edge_vertex i) a) = a := by
  exact Finsupp.lsum_single (ZMod 2)
    (fun _ : Face edgeK 0 => LinearMap.id) _ _

private theorem edge_coeffSum_boundary :
    edge_coeffSum.comp (boundary edgeK (ZMod 2) 0) = 0 := by
  apply Finsupp.lhom_ext
  intro σ a
  have hσ : σ = edge_face := edge_face_unique σ
  subst σ
  change edge_coeffSum (boundary edgeK (ZMod 2) 0
      (Finsupp.single edge_face a)) = 0
  rw [edge_boundary, map_sub, edge_coeffSum_single, edge_coeffSum_single]
  exact sub_self a

private theorem edge_coeffSum_coords (c : Chain edgeK (ZMod 2) 0) :
    edge_coeffSum c = c (edge_vertex 0) + c (edge_vertex 1) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, Finsupp.add_apply, hc, hd, add_add_add_comm]
  | single v a =>
      obtain ⟨i, rfl⟩ := edge_vertex_bijective.2 v
      fin_cases i
      · simp [edge_coeffSum_single, edge_vertex_ne]
      · simp [edge_coeffSum_single, edge_vertex_ne.symm]

private theorem edge_chain_decompose (c : Chain edgeK (ZMod 2) 0) :
    c - Finsupp.single (edge_vertex 0) (edge_coeffSum c) =
      boundary edgeK (ZMod 2) 0
        (Finsupp.single edge_face (c (edge_vertex 1))) := by
  rw [edge_boundary]
  apply Finsupp.ext
  intro v
  obtain ⟨i, rfl⟩ := edge_vertex_bijective.2 v
  fin_cases i
  · simp [edge_coeffSum_coords, edge_vertex_ne, edge_vertex_ne.symm,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have htwo : c (edge_vertex 0) + c (edge_vertex 0) = 0 := by
      simpa [ZMod.neg_eq_self_mod_two] using
        (add_neg_cancel (c (edge_vertex 0)))
    rw [← add_assoc, htwo, zero_add]
  · simp [edge_vertex_ne, edge_vertex_ne.symm]

private noncomputable def edge_vertex0_cycle : simplicialCycles edgeK (ZMod 2) 0 :=
  ⟨Finsupp.single (edge_vertex 0) 1, by rw [simplicialCycles_zero]; trivial⟩

private theorem edge_vertex0_not_boundary :
    edge_vertex0_cycle ∉ simplicialBoundaries edgeK (ZMod 2) 0 := by
  intro hz
  obtain ⟨c, hc⟩ :=
    (mem_simplicialBoundaries_iff (ZMod 2) edgeK 0 edge_vertex0_cycle).1 hz
  have hs := congrArg edge_coeffSum hc
  have hzero := congrArg (fun f : Chain edgeK (ZMod 2) 1 →ₗ[ZMod 2] ZMod 2 => f c)
    edge_coeffSum_boundary
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
  rw [hzero] at hs
  change 0 = edge_coeffSum (Finsupp.single (edge_vertex 0) 1) at hs
  rw [edge_coeffSum_single] at hs
  exact one_ne_zero hs.symm

private theorem edge_vertex0_class_nonzero :
    (simplicialBoundaries edgeK (ZMod 2) 0).mkQ edge_vertex0_cycle ≠ 0 := by
  intro hz
  exact edge_vertex0_not_boundary
    ((Submodule.Quotient.mk_eq_zero _).1 hz)

private noncomputable def edge_vertex1_cycle : simplicialCycles edgeK (ZMod 2) 0 :=
  ⟨Finsupp.single (edge_vertex 1) 1, by rw [simplicialCycles_zero]; trivial⟩

private theorem edge_vertex1_not_boundary :
    edge_vertex1_cycle ∉ simplicialBoundaries edgeK (ZMod 2) 0 := by
  intro hz
  obtain ⟨c, hc⟩ :=
    (mem_simplicialBoundaries_iff (ZMod 2) edgeK 0 edge_vertex1_cycle).1 hz
  have hs := congrArg edge_coeffSum hc
  have hzero := congrArg (fun f : Chain edgeK (ZMod 2) 1 →ₗ[ZMod 2] ZMod 2 => f c)
    edge_coeffSum_boundary
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hzero
  rw [hzero] at hs
  change 0 = edge_coeffSum (Finsupp.single (edge_vertex 1) 1) at hs
  rw [edge_coeffSum_single] at hs
  exact one_ne_zero hs.symm

private theorem edge_vertex1_class_nonzero :
    (simplicialBoundaries edgeK (ZMod 2) 0).mkQ edge_vertex1_cycle ≠ 0 := by
  intro hz
  exact edge_vertex1_not_boundary
    ((Submodule.Quotient.mk_eq_zero _).1 hz)

private theorem edge_singleton_le : singletonFace (0 : Fin 2) ≤ edgeK := by
  intro s hs
  have h : s = ({0} : Finset (Fin 2)) :=
    (mem_singletonFace_iff 0 s).1 hs
  subst s
  change ({0} : Finset (Fin 2)).Nonempty
  simp

private theorem edge_two_le : edge_twoVertices ≤ edgeK := by
  intro s hs
  rcases (show s = ({0} : Finset (Fin 2)) ∨ s = {1} from hs) with h | h
  · subst s
    change ({0} : Finset (Fin 2)).Nonempty
    simp
  · subst s
    change ({1} : Finset (Fin 2)).Nonempty
    simp

private theorem edge_coeffSum_chainIncl :
    edge_coeffSum.comp (chainIncl (ZMod 2) edge_two_le 0) =
      edgeTwo_coeffSum := by
  apply Finsupp.lhom_ext
  intro σ a
  obtain ⟨i, rfl⟩ := edge_twoVertex_bijective.2 σ
  change edge_coeffSum
      (chainIncl (ZMod 2) edge_two_le 0
        (Finsupp.single (edge_twoVertex i) a)) =
    edgeTwo_coeffSum (Finsupp.single (edge_twoVertex i) a)
  rw [chainIncl_single]
  have hface : faceIncl edge_two_le 0 (edge_twoVertex i) = edge_vertex i :=
    Subtype.ext rfl
  rw [hface, edge_coeffSum_single]
  exact (Finsupp.lsum_single (ZMod 2)
    (fun _ : Face edge_twoVertices 0 => LinearMap.id) _ _).symm

private noncomputable instance edgeTwo_cyclesHasQuotient :
    HasQuotient (simplicialCycles edge_twoVertices (ZMod 2) 0)
      (Submodule (ZMod 2) (simplicialCycles edge_twoVertices (ZMod 2) 0)) :=
  Submodule.hasQuotient (R := ZMod 2)
    (M := simplicialCycles edge_twoVertices (ZMod 2) 0)

private noncomputable def edgeTwo_cycleOf
    (x : (simplicialChainComplex edge_twoVertices (ZMod 2)).homology 0) :
    simplicialCycles edge_twoVertices (ZMod 2) 0 :=
  ⟨edgeTwoH0Equiv x, by rw [simplicialCycles_zero]; trivial⟩

private theorem edge_singleton_two : singletonFace (0 : Fin 2) ≤ edge_twoVertices :=
  le_sup_left

private theorem edge_first_two_chain_square
    (x : simplicialHomology (singletonFace (0 : Fin 2)) (ZMod 2) 0) :
    edgeTwoH0Equiv
        ((simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom x) =
      chainIncl (ZMod 2) edge_singleton_two 0 (edgeOneH0Equiv x) := by
  let φ : (simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)).sc 0 ⟶
      (simplicialChainComplex edge_twoVertices (ZMod 2)).sc 0 :=
    (HomologicalComplex.shortComplexFunctor _ _ 0).map
      (simplicialChainIncl (ZMod 2) edge_singleton_two)
  have h := (ShortComplex.LeftHomologyMapData.ofZeros φ
    edgeOne_short_f_zero edgeOne_short_g_zero
    edgeTwo_short_f_zero edgeTwo_short_g_zero).homologyMap_comm
  have hx := congrArg (fun f => f.hom x) h
  change edgeTwoH0Equiv
      ((simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom x) =
    chainIncl (ZMod 2) edge_singleton_two 0 (edgeOneH0Equiv x) at hx
  exact hx

private noncomputable def edgeOneScalarEquiv :
    simplicialHomology (singletonFace (0 : Fin 2)) (ZMod 2) 0 ≃ₗ[ZMod 2] ZMod 2 :=
  edgeOneH0Equiv.trans
    (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2) (singletonVertex (0 : Fin 2)))

private theorem edge_first_two_pair_coordinates (a : ZMod 2) :
    edgeTwoPairEquiv
      ((simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom
        (edgeOneScalarEquiv.symm a)) =
      (a, 0) := by
  let x := edgeOneScalarEquiv.symm a
  have hchain : edgeOneH0Equiv x =
      Finsupp.single (singletonVertex (0 : Fin 2)) a := by
    apply (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2)
      (singletonVertex (0 : Fin 2))).injective
    have hx : edgeOneScalarEquiv x = a :=
      LinearEquiv.apply_symm_apply _ _
    simpa only [edgeOneScalarEquiv, LinearEquiv.trans_apply,
      Finsupp.uniqueLinearEquiv_apply, Finsupp.single_eq_same] using hx
  have hface : faceIncl edge_singleton_two 0
      (singletonVertex (0 : Fin 2)) = edge_twoVertex 0 := Subtype.ext rfl
  have hmap := edge_first_two_chain_square x
  rw [hchain, chainIncl_single, hface] at hmap
  rw [edgeTwoPairEquiv_apply, hmap]
  simp [edge_twoVertex_ne, edge_twoVertex_ne.symm]

private theorem edge_other_two : singletonFace (1 : Fin 2) ≤ edge_twoVertices :=
  le_sup_right

private theorem edge_other_two_chain_square
    (x : simplicialHomology (singletonFace (1 : Fin 2)) (ZMod 2) 0) :
    edgeTwoH0Equiv
        ((simplicialHomologyIncl (ZMod 2) edge_other_two 0).hom x) =
      chainIncl (ZMod 2) edge_other_two 0 (edgeOtherH0Equiv x) := by
  let φ : (simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)).sc 0 ⟶
      (simplicialChainComplex edge_twoVertices (ZMod 2)).sc 0 :=
    (HomologicalComplex.shortComplexFunctor _ _ 0).map
      (simplicialChainIncl (ZMod 2) edge_other_two)
  have h := (ShortComplex.LeftHomologyMapData.ofZeros φ
    edgeOther_short_f_zero edgeOther_short_g_zero
    edgeTwo_short_f_zero edgeTwo_short_g_zero).homologyMap_comm
  have hx := congrArg (fun f => f.hom x) h
  change edgeTwoH0Equiv
      ((simplicialHomologyIncl (ZMod 2) edge_other_two 0).hom x) =
    chainIncl (ZMod 2) edge_other_two 0 (edgeOtherH0Equiv x) at hx
  exact hx

private noncomputable def edgeOtherScalarEquiv :
    simplicialHomology (singletonFace (1 : Fin 2)) (ZMod 2) 0 ≃ₗ[ZMod 2] ZMod 2 :=
  edgeOtherH0Equiv.trans
    (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2) (singletonVertex (1 : Fin 2)))

private theorem edge_other_two_pair_coordinates (a : ZMod 2) :
    edgeTwoPairEquiv
      ((simplicialHomologyIncl (ZMod 2) edge_other_two 0).hom
        (edgeOtherScalarEquiv.symm a)) =
      (0, a) := by
  let x := edgeOtherScalarEquiv.symm a
  have hchain : edgeOtherH0Equiv x =
      Finsupp.single (singletonVertex (1 : Fin 2)) a := by
    apply (Finsupp.uniqueLinearEquiv (ZMod 2) (ZMod 2)
      (singletonVertex (1 : Fin 2))).injective
    have hx : edgeOtherScalarEquiv x = a :=
      LinearEquiv.apply_symm_apply _ _
    simpa only [edgeOtherScalarEquiv, LinearEquiv.trans_apply,
      Finsupp.uniqueLinearEquiv_apply, Finsupp.single_eq_same] using hx
  have hface : faceIncl edge_other_two 0
      (singletonVertex (1 : Fin 2)) = edge_twoVertex 1 := Subtype.ext rfl
  have hmap := edge_other_two_chain_square x
  rw [hchain, chainIncl_single, hface] at hmap
  rw [edgeTwoPairEquiv_apply, hmap]
  simp [edge_twoVertex_ne, edge_twoVertex_ne.symm]

private noncomputable def edge_source_cycle :
    simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0 :=
  ⟨Finsupp.single (singletonVertex (0 : Fin 2)) 1, by
    rw [simplicialCycles_zero]; trivial⟩

private theorem edge_cycle_inclusion :
    simplicialCycleIncl (ZMod 2) edge_singleton_le 0 edge_source_cycle =
      edge_vertex0_cycle := by
  apply Subtype.ext
  rw [simplicialCycleIncl_coe]
  change chainIncl (ZMod 2) edge_singleton_le 0
      (Finsupp.single (singletonVertex (0 : Fin 2)) 1) =
    Finsupp.single (edge_vertex 0) 1
  rw [chainIncl_single]
  have hface : faceIncl edge_singleton_le 0 (singletonVertex (0 : Fin 2)) =
      edge_vertex 0 := Subtype.ext rfl
  rw [hface]

private theorem edge_singleton_map_nonzero :
    (simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom ≠ 0 := by
  letI : HasQuotient (simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0)
      (Submodule (ZMod 2)
        (simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2)
      (M := simplicialCycles (singletonFace (0 : Fin 2)) (ZMod 2) 0)
  letI : HasQuotient (simplicialCycles edgeK (ZMod 2) 0)
      (Submodule (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2)
      (M := simplicialCycles edgeK (ZMod 2) 0)
  let q := (simplicialBoundaries (singletonFace (0 : Fin 2)) (ZMod 2) 0).mkQ
    edge_source_cycle
  let e0 := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex (singletonFace (0 : Fin 2)) (ZMod 2)) 0).toLinearEquiv
  let e1 := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv
  let x := e0.symm q
  have hnat : e1 ((simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom x) =
      (simplicialBoundaries edgeK (ZMod 2) 0).mkQ edge_vertex0_cycle := by
    have hh := simplicialHomologyIncl_quotient_naturality
      (ZMod 2) edge_singleton_le 0
    have hx := congrArg (fun f : simplicialHomology
      (singletonFace (0 : Fin 2)) (ZMod 2) 0 ⟶
      ModuleCat.of (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0 ⧸
        simplicialBoundaries edgeK (ZMod 2) 0) => f.hom x) hh
    change e1 ((simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom x) =
      simplicialQuotientIncl (ZMod 2) edge_singleton_le 0 (e0 x) at hx
    rw [show e0 x = q from e0.apply_symm_apply q,
      simplicialQuotientIncl_mkQ, edge_cycle_inclusion] at hx
    exact hx
  intro hz
  rw [hz] at hnat
  change e1 (0 : simplicialHomology edgeK (ZMod 2) 0) = _ at hnat
  have he : e1 (0 : simplicialHomology edgeK (ZMod 2) 0) = 0 := e1.map_zero
  exact edge_vertex0_class_nonzero (hnat.symm.trans he)

private theorem edge_other_le : singletonFace (1 : Fin 2) ≤ edgeK := by
  intro t ht
  have h : t = ({1} : Finset (Fin 2)) := (mem_singletonFace_iff 1 t).1 ht
  subst t
  change ({1} : Finset (Fin 2)).Nonempty
  simp

private noncomputable def edge_other_source_cycle :
    simplicialCycles (singletonFace (1 : Fin 2)) (ZMod 2) 0 :=
  ⟨Finsupp.single (singletonVertex (1 : Fin 2)) 1, by
    rw [simplicialCycles_zero]; trivial⟩

private theorem edge_other_cycle_inclusion :
    simplicialCycleIncl (ZMod 2) edge_other_le 0 edge_other_source_cycle =
      edge_vertex1_cycle := by
  apply Subtype.ext
  rw [simplicialCycleIncl_coe]
  change chainIncl (ZMod 2) edge_other_le 0
      (Finsupp.single (singletonVertex (1 : Fin 2)) 1) =
    Finsupp.single (edge_vertex 1) 1
  rw [chainIncl_single]
  have hface : faceIncl edge_other_le 0 (singletonVertex (1 : Fin 2)) =
      edge_vertex 1 := Subtype.ext rfl
  rw [hface]

private theorem edge_other_map_nonzero :
    (simplicialHomologyIncl (ZMod 2) edge_other_le 0).hom ≠ 0 := by
  letI : HasQuotient (simplicialCycles (singletonFace (1 : Fin 2)) (ZMod 2) 0)
      (Submodule (ZMod 2)
        (simplicialCycles (singletonFace (1 : Fin 2)) (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2)
      (M := simplicialCycles (singletonFace (1 : Fin 2)) (ZMod 2) 0)
  letI : HasQuotient (simplicialCycles edgeK (ZMod 2) 0)
      (Submodule (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0)) :=
    Submodule.hasQuotient (R := ZMod 2)
      (M := simplicialCycles edgeK (ZMod 2) 0)
  let q := (simplicialBoundaries (singletonFace (1 : Fin 2)) (ZMod 2) 0).mkQ
    edge_other_source_cycle
  let e0 := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex (singletonFace (1 : Fin 2)) (ZMod 2)) 0).toLinearEquiv
  let e1 := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv
  let x := e0.symm q
  have hnat : e1 ((simplicialHomologyIncl (ZMod 2) edge_other_le 0).hom x) =
      (simplicialBoundaries edgeK (ZMod 2) 0).mkQ edge_vertex1_cycle := by
    have hh := simplicialHomologyIncl_quotient_naturality
      (ZMod 2) edge_other_le 0
    have hx := congrArg (fun f : simplicialHomology
      (singletonFace (1 : Fin 2)) (ZMod 2) 0 ⟶
      ModuleCat.of (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0 ⧸
        simplicialBoundaries edgeK (ZMod 2) 0) => f.hom x) hh
    change e1 ((simplicialHomologyIncl (ZMod 2) edge_other_le 0).hom x) =
      simplicialQuotientIncl (ZMod 2) edge_other_le 0 (e0 x) at hx
    rw [show e0 x = q from e0.apply_symm_apply q,
      simplicialQuotientIncl_mkQ, edge_other_cycle_inclusion] at hx
    exact hx
  intro hz
  rw [hz] at hnat
  change e1 (0 : simplicialHomology edgeK (ZMod 2) 0) = _ at hnat
  have he : e1 (0 : simplicialHomology edgeK (ZMod 2) 0) = 0 := e1.map_zero
  exact edge_vertex1_class_nonzero (hnat.symm.trans he)

private theorem edge_map_comp :
    simplicialHomologyIncl (ZMod 2) edge_singleton_le 0 =
      simplicialHomologyIncl (ZMod 2) edge_singleton_two 0 ≫
        simplicialHomologyIncl (ZMod 2) edge_two_le 0 := by
  have h : edge_singleton_le = edge_singleton_two.trans edge_two_le :=
    Subsingleton.elim _ _
  rw [h]
  exact simplicialHomologyIncl_comp (ZMod 2) edge_singleton_two edge_two_le 0

private theorem edge_singleton_two_nonzero :
    (simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom ≠ 0 := by
  intro hz
  apply edge_singleton_map_nonzero
  have hc := congrArg (fun f : simplicialHomology
    (singletonFace (0 : Fin 2)) (ZMod 2) 0 ⟶
    simplicialHomology edgeK (ZMod 2) 0 => f.hom) edge_map_comp
  simpa [hz] using hc

private theorem edge_two_full_nonzero :
    (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom ≠ 0 := by
  intro hz
  apply edge_singleton_map_nonzero
  have hc := congrArg (fun f : simplicialHomology
    (singletonFace (0 : Fin 2)) (ZMod 2) 0 ⟶
    simplicialHomology edgeK (ZMod 2) 0 => f.hom) edge_map_comp
  simpa [hz] using hc

private theorem rank_one_of_nonzero
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

private theorem edge_rank_01 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom) = 1 := by
  exact rank_one_of_nonzero
    ((simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
      (Module.finrank_self (ZMod 2))) _ edge_singleton_two_nonzero

private theorem edge_rank_02 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom) = 1 := by
  exact rank_one_of_nonzero
    ((simplicialSingletonH0Equiv (ZMod 2) (0 : Fin 2)).finrank_eq.trans
      (Module.finrank_self (ZMod 2))) _ edge_singleton_map_nonzero

private theorem edge_rank_12 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom) = 1 := by
  have hle := LinearMap.finrank_range_le
    (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom
  have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    have hx : ∃ x, (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom x ≠ 0 := by
      by_contra h
      apply edge_two_full_nonzero
      ext x
      simpa using (not_not.mp (not_exists.mp h x))
    obtain ⟨x, hx⟩ := hx
    refine ⟨⟨_, ⟨x, rfl⟩⟩, ?_⟩
    exact fun he => hx (congrArg Subtype.val he)
  have htarget : Module.finrank (ZMod 2)
      (simplicialHomology edgeK (ZMod 2) 0) = 1 := by
    have hh := edge_H0_stage2
    change Module.finrank (ZMod 2)
      (simplicialHomology (edgeFilter.gradeFiltration edge_i2) (ZMod 2) 0) = 1 at hh
    rw [edge_stage2] at hh
    exact hh
  have hle' := Submodule.finrank_le
    (LinearMap.range (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom)
  rw [htarget] at hle'
  omega

private theorem edge_rank_congr {A B A' B' : PreAbstractSimplicialComplex (Fin 2)}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) h 0).hom) =
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) h' 0).hom) := by
  cases hA
  cases hB
  rfl

private theorem edge_grade_rank_00 (h : edge_i0 ≤ edge_i0) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      edgeFilter.gradeFiltration 0) edge_i0 edge_i0 h = 1 := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact edge_H0_stage0

private theorem edge_grade_rank_11 (h : edge_i1 ≤ edge_i1) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      edgeFilter.gradeFiltration 0) edge_i1 edge_i1 h = 2 := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact edge_H0_stage1

private theorem edge_grade_rank_22 (h : edge_i2 ≤ edge_i2) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      edgeFilter.gradeFiltration 0) edge_i2 edge_i2 h = 1 := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]
  exact edge_H0_stage2

private theorem edge_grade_rank_01 (h : edge_i0 ≤ edge_i1) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      edgeFilter.gradeFiltration 0) edge_i0 edge_i1 h = 1 := by
  change Module.finrank (ZMod 2) (LinearMap.range
    (simplicialHomologyIncl (ZMod 2) (edgeFilter.gradeFiltration.monotone h) 0).hom) = 1
  exact (edge_rank_congr edge_stage0 edge_stage1 _ edge_singleton_two).trans
    edge_rank_01

private theorem edge_grade_rank_02 (h : edge_i0 ≤ edge_i2) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      edgeFilter.gradeFiltration 0) edge_i0 edge_i2 h = 1 := by
  change Module.finrank (ZMod 2) (LinearMap.range
    (simplicialHomologyIncl (ZMod 2) (edgeFilter.gradeFiltration.monotone h) 0).hom) = 1
  exact (edge_rank_congr edge_stage0 edge_stage2 _ edge_singleton_le).trans
    edge_rank_02

private theorem edge_grade_rank_12 (h : edge_i1 ≤ edge_i2) :
    structureMapRank (simplicialHomologyPModule (ZMod 2)
      edgeFilter.gradeFiltration 0) edge_i1 edge_i2 h = 1 := by
  change Module.finrank (ZMod 2) (LinearMap.range
    (simplicialHomologyIncl (ZMod 2) (edgeFilter.gradeFiltration.monotone h) 0).hom) = 1
  exact (edge_rank_congr edge_stage1 edge_stage2 _ edge_two_le).trans
    edge_rank_12

private noncomputable def edge_bar03 : FiniteInterval edgeFilter.criticalValues.card :=
  ⟨0, 3, by omega, by rw [edge_card]⟩

private noncomputable def edge_bar12 : FiniteInterval edgeFilter.criticalValues.card :=
  ⟨1, 2, by omega, by rw [edge_card]; decide⟩

private theorem edge_barcode :
    gradeHomologyBarcode (ZMod 2) edgeFilter 0 =
      ({edge_bar03, edge_bar12} :
        Multiset (FiniteInterval edgeFilter.criticalValues.card)) := by
  calc
    gradeHomologyBarcode (ZMod 2) edgeFilter 0 =
        rankBarcode (barcodeModule (k := ZMod 2)
          ({edge_bar03, edge_bar12} :
            Multiset (FiniteInterval edgeFilter.criticalValues.card))) := by
      apply (rankBarcode_eq_iff
        (simplicialHomologyPModule (ZMod 2) edgeFilter.gradeFiltration 0)
        (barcodeModule (k := ZMod 2)
          ({edge_bar03, edge_bar12} :
            Multiset (FiniteInterval edgeFilter.criticalValues.card)))).mpr
      intro i j hij
      have hi : i = edge_i0 ∨ i = edge_i1 ∨ i = edge_i2 := by
        have hv := i.isLt
        have hc := edge_card
        rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 by omega) with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      have hj : j = edge_i0 ∨ j = edge_i1 ∨ j = edge_i2 := by
        have hv := j.isLt
        have hc := edge_card
        rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 by omega) with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      all_goals simp only [edge_i0, edge_i1, edge_i2, Fin.mk_le_mk] at hij
      all_goals simp at hij
      all_goals rw [rank_barcodeMap]
      all_goals first
        | rw [edge_grade_rank_00]
        | rw [edge_grade_rank_01]
        | rw [edge_grade_rank_02]
        | rw [edge_grade_rank_11]
        | rw [edge_grade_rank_12]
        | rw [edge_grade_rank_22]
      all_goals
        rw [show ({edge_bar03, edge_bar12} :
          Multiset (FiniteInterval edgeFilter.criticalValues.card)) =
            edge_bar03 ::ₘ edge_bar12 ::ₘ 0 by rfl,
          Multiset.countP_cons, Multiset.countP_cons]
        simp [edge_bar03, edge_bar12, edge_i0, edge_i1, edge_i2]
      all_goals rfl
    _ = _ := rankBarcode_barcodeModule _

private theorem edge_points :
    (dgm (ZMod 2) edgeFilter 0).points =
      ({((2 : ℝ), (⊤ : WithTop ℝ)), ((5 : ℝ), (9 : WithTop ℝ))} :
        Multiset (ℝ × WithTop ℝ)) := by
  rw [dgm, edge_barcode]
  change ({edge_bar03, edge_bar12} :
    Multiset (FiniteInterval edgeFilter.criticalValues.card)).map
      (fun I =>
        (edgeFilter.criticalValue
          ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
          if hd : I.death < edgeFilter.criticalValues.card then
            (edgeFilter.criticalValue ⟨I.death, hd⟩ : WithTop ℝ)
          else (⊤ : WithTop ℝ))) = _
  simp [edge_bar03, edge_bar12, edge_card]
  have hc0 : ∀ h : 0 < edgeFilter.criticalValues.card,
      edgeFilter.criticalValue ⟨0, h⟩ = 2 := by
    intro h
    have he : (⟨0, h⟩ : Fin edgeFilter.criticalValues.card) = edge_i0 := Fin.ext rfl
    rw [he]
    exact edge_critical.1
  have hc1 : ∀ h : 1 < edgeFilter.criticalValues.card,
      edgeFilter.criticalValue ⟨1, h⟩ = 5 := by
    intro h
    have he : (⟨1, h⟩ : Fin edgeFilter.criticalValues.card) = edge_i1 := Fin.ext rfl
    rw [he]
    exact edge_critical.2.1
  have hc2 : ∀ h : 2 < edgeFilter.criticalValues.card,
      edgeFilter.criticalValue ⟨2, h⟩ = 9 := by
    intro h
    have he : (⟨2, h⟩ : Fin edgeFilter.criticalValues.card) = edge_i2 := Fin.ext rfl
    rw [he]
    exact edge_critical.2.2
  simp [hc0, hc1, hc2]

private theorem edge_rank_and_count (r s : ℝ) (hrs : r ≤ s) (m : ℕ)
    (hc : ({((2 : ℝ), (⊤ : WithTop ℝ)), ((5 : ℝ), (9 : WithTop ℝ))} :
      Multiset (ℝ × WithTop ℝ)).countP
        (fun p => p.1 ≤ r ∧ (s : WithTop ℝ) < p.2) = m) :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2) (edgeFilter.sublevel_mono hrs) 0).hom) = m ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ r ∧ (s : WithTop ℝ) < p.2) = m := by
  have h := rank_sublevelHomologyMap (ZMod 2) edgeFilter 0 r s hrs
  rw [edge_points] at h
  exact ⟨h.trans hc, by rw [edge_points]; exact hc⟩

private theorem edge_count_formula (r s : ℝ) :
    ({((2 : ℝ), (⊤ : WithTop ℝ)), ((5 : ℝ), (9 : WithTop ℝ))} :
      Multiset (ℝ × WithTop ℝ)).countP
        (fun p => p.1 ≤ r ∧ (s : WithTop ℝ) < p.2) =
      (if (2 : ℝ) ≤ r then 1 else 0) +
        (if (5 : ℝ) ≤ r ∧ s < 9 then 1 else 0) := by
  rw [show ({((2 : ℝ), (⊤ : WithTop ℝ)), ((5 : ℝ), (9 : WithTop ℝ))} :
    Multiset (ℝ × WithTop ℝ)) =
      ((2 : ℝ), (⊤ : WithTop ℝ)) ::ₘ ((5 : ℝ), (9 : WithTop ℝ)) ::ₘ 0 by rfl,
    Multiset.countP_cons, Multiset.countP_cons]
  simp only [Multiset.countP_zero, zero_add, WithTop.coe_lt_coe, WithTop.coe_lt_top,
    and_true]
  have h9 : (s : WithTop ℝ) < (9 : WithTop ℝ) ↔ s < (9 : ℝ) := by
    exact WithTop.coe_lt_coe
  simp only [h9]
  exact Nat.add_comm (if (5 : ℝ) ≤ r ∧ s < 9 then 1 else 0)
    (if (2 : ℝ) ≤ r then 1 else 0)

private theorem edge_row_1_10 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (1 : ℝ) ≤ 10 by norm_num)) 0).hom) = 0 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (1 : ℝ) ∧ ((10 : ℝ) : WithTop ℝ) < p.2) = 0 := by
  refine edge_rank_and_count 1 10 (by norm_num) 0 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_1_1 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (le_refl (1 : ℝ))) 0).hom) = 0 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (1 : ℝ) ∧ ((1 : ℝ) : WithTop ℝ) < p.2) = 0 := by
  refine edge_rank_and_count 1 1 le_rfl 0 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_1_3 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (1 : ℝ) ≤ 3 by norm_num)) 0).hom) = 0 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (1 : ℝ) ∧ ((3 : ℝ) : WithTop ℝ) < p.2) = 0 := by
  refine edge_rank_and_count 1 3 (by norm_num) 0 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_2_2 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (le_refl (2 : ℝ))) 0).hom) = 1 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (2 : ℝ) ∧ ((2 : ℝ) : WithTop ℝ) < p.2) = 1 := by
  refine edge_rank_and_count 2 2 le_rfl 1 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_9_9 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (le_refl (9 : ℝ))) 0).hom) = 1 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (9 : ℝ) ∧ ((9 : ℝ) : WithTop ℝ) < p.2) = 1 := by
  refine edge_rank_and_count 9 9 le_rfl 1 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_6_10 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (6 : ℝ) ≤ 10 by norm_num)) 0).hom) = 1 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (6 : ℝ) ∧ ((10 : ℝ) : WithTop ℝ) < p.2) = 1 := by
  refine edge_rank_and_count 6 10 (by norm_num) 1 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_finite_death_endpoint :
    ((5 : ℝ), (9 : WithTop ℝ)) ∈ (dgm (ZMod 2) edgeFilter 0).points ∧
      ((5 : ℝ) ≤ 6 ∧ (8 : WithTop ℝ) < (9 : WithTop ℝ)) ∧
      ¬ ((5 : ℝ) ≤ 6 ∧ (9 : WithTop ℝ) < (9 : WithTop ℝ)) := by
  rw [edge_points]
  norm_num
  exact WithTop.coe_lt_coe.mpr (show (8 : ℝ) < 9 by norm_num)

private theorem edge_row_3_4 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 4 by norm_num)) 0).hom) = 1 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (3 : ℝ) ∧ ((4 : ℝ) : WithTop ℝ) < p.2) = 1 := by
  refine edge_rank_and_count 3 4 (by norm_num) 1 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_3_6 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 6 by norm_num)) 0).hom) = 1 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (3 : ℝ) ∧ ((6 : ℝ) : WithTop ℝ) < p.2) = 1 := by
  refine edge_rank_and_count 3 6 (by norm_num) 1 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_5_5 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (le_refl (5 : ℝ))) 0).hom) = 2 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (5 : ℝ) ∧ ((5 : ℝ) : WithTop ℝ) < p.2) = 2 := by
  refine edge_rank_and_count 5 5 (by norm_num) 2 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_6_8 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (6 : ℝ) ≤ 8 by norm_num)) 0).hom) = 2 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (6 : ℝ) ∧ ((8 : ℝ) : WithTop ℝ) < p.2) = 2 := by
  refine edge_rank_and_count 6 8 (by norm_num) 2 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_6_9 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (6 : ℝ) ≤ 9 by norm_num)) 0).hom) = 1 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (6 : ℝ) ∧ ((9 : ℝ) : WithTop ℝ) < p.2) = 1 := by
  refine edge_rank_and_count 6 9 (by norm_num) 1 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_row_10_11 :
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (10 : ℝ) ≤ 11 by norm_num)) 0).hom) = 1 ∧
    (dgm (ZMod 2) edgeFilter 0).points.countP
      (fun p => p.1 ≤ (10 : ℝ) ∧ ((11 : ℝ) : WithTop ℝ) < p.2) = 1 := by
  refine edge_rank_and_count 10 11 (by norm_num) 1 ?_
  rw [edge_count_formula]
  norm_num

private theorem edge_target6_dim :
    Module.finrank (ZMod 2)
      (simplicialHomology (edgeFilter.sublevel (6 : ℝ)) (ZMod 2) 0) = 2 := by
  rw [edge_region1 6 (by norm_num) (by norm_num)]
  have hh := edge_H0_stage1
  change Module.finrank (ZMod 2)
    (simplicialHomology (edgeFilter.gradeFiltration edge_i1) (ZMod 2) 0) = 2 at hh
  rw [edge_stage1] at hh
  exact hh

private theorem edge_rank_target_discriminator :
    Module.finrank (ZMod 2)
      (simplicialHomology (edgeFilter.sublevel (6 : ℝ)) (ZMod 2) 0) = 2 ∧
    Module.finrank (ZMod 2) (LinearMap.range
      (simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 6 by norm_num)) 0).hom) = 1 :=
  ⟨edge_target6_dim, edge_row_3_6.1⟩

private theorem edge_identity_3_4 :
    simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 4 by norm_num)) 0 ≫
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region0 4 (by norm_num) (by norm_num))) =
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region0 3 (by norm_num) (by norm_num))) := by
  exact same_complex_identity
    (edge_region0 3 (by norm_num) (by norm_num))
    (edge_region0 4 (by norm_num) (by norm_num)) _

private theorem edge_identity_6_8 :
    simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (6 : ℝ) ≤ 8 by norm_num)) 0 ≫
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region1 8 (by norm_num) (by norm_num))) =
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region1 6 (by norm_num) (by norm_num))) := by
  exact same_complex_identity
    (edge_region1 6 (by norm_num) (by norm_num))
    (edge_region1 8 (by norm_num) (by norm_num)) _

private theorem edge_identity_10_11 :
    simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (10 : ℝ) ≤ 11 by norm_num)) 0 ≫
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region2 11 (by norm_num))) =
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region2 10 (by norm_num))) := by
  exact same_complex_identity
    (edge_region2 10 (by norm_num)) (edge_region2 11 (by norm_num)) _

private theorem edge_two_step_3_6_10 :
    simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 10 by norm_num)) 0 =
      simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 6 by norm_num)) 0 ≫
      simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (6 : ℝ) ≤ 10 by norm_num)) 0 := by
  have h := simplicialHomologyIncl_comp (ZMod 2)
    (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 6 by norm_num))
    (edgeFilter.sublevel_mono (show (6 : ℝ) ≤ 10 by norm_num)) 0
  simpa using h

private theorem edge_incl_eq_square {A B A' B' : PreAbstractSimplicialComplex (Fin 2)}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') :
    simplicialHomologyIncl (ZMod 2) h 0 ≫
        eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) hB) =
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0) hA) ≫
        simplicialHomologyIncl (ZMod 2) h' 0 := by
  subst A'
  subst B'
  simp

private theorem edge_transported_two_step_3_6_10 :
    simplicialHomologyIncl (ZMod 2)
        (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 10 by norm_num)) 0 ≫
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region2 10 (by norm_num))) =
      eqToHom (congrArg (fun C => simplicialHomology C (ZMod 2) 0)
        (edge_region0 3 (by norm_num) (by norm_num))) ≫
        (simplicialHomologyIncl (ZMod 2) edge_singleton_two 0 ≫
          simplicialHomologyIncl (ZMod 2) edge_two_le 0) := by
  have h36 := edge_incl_eq_square
    (edge_region0 3 (by norm_num) (by norm_num))
    (edge_region1 6 (by norm_num) (by norm_num))
    (edgeFilter.sublevel_mono (show (3 : ℝ) ≤ 6 by norm_num)) edge_singleton_two
  have h610 := edge_incl_eq_square
    (edge_region1 6 (by norm_num) (by norm_num))
    (edge_region2 10 (by norm_num))
    (edgeFilter.sublevel_mono (show (6 : ℝ) ≤ 10 by norm_num)) edge_two_le
  rw [edge_two_step_3_6_10, Category.assoc, h610,
    ← Category.assoc, h36, Category.assoc]

private noncomputable def edge_cycleSum :
    simplicialCycles edgeK (ZMod 2) 0 →ₗ[ZMod 2] ZMod 2 :=
  edge_coeffSum.comp (simplicialCycles edgeK (ZMod 2) 0).subtype

private theorem edge_boundaries_ker_cycleSum :
    simplicialBoundaries edgeK (ZMod 2) 0 ≤ LinearMap.ker edge_cycleSum := by
  intro z hz
  obtain ⟨c, hc⟩ :=
    (mem_simplicialBoundaries_iff (ZMod 2) edgeK 0 z).1 hz
  change edge_cycleSum z = 0
  change edge_coeffSum (z : Chain edgeK (ZMod 2) 0) = 0
  rw [← hc]
  have hh := congrArg (fun f : Chain edgeK (ZMod 2) 1 →ₗ[ZMod 2] ZMod 2 => f c)
    edge_coeffSum_boundary
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using hh

private noncomputable instance edge_cyclesHasQuotient :
    HasQuotient (simplicialCycles edgeK (ZMod 2) 0)
      (Submodule (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0)) :=
  Submodule.hasQuotient (R := ZMod 2)
    (M := simplicialCycles edgeK (ZMod 2) 0)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def edge_quotSum :
    (simplicialCycles edgeK (ZMod 2) 0 ⧸
      simplicialBoundaries edgeK (ZMod 2) 0) →ₗ[ZMod 2] ZMod 2 := by
  let p : Submodule (ZMod 2) (simplicialCycles edgeK (ZMod 2) 0) :=
    simplicialBoundaries edgeK (ZMod 2) 0
  let f : simplicialCycles edgeK (ZMod 2) 0 →ₗ[ZMod 2] ZMod 2 := edge_cycleSum
  have h : p ≤ LinearMap.ker f := edge_boundaries_ker_cycleSum
  exact p.liftQ f h

private noncomputable def edge_H0_sum :
    simplicialHomology edgeK (ZMod 2) 0 →ₗ[ZMod 2] ZMod 2 :=
  edge_quotSum.comp
    (homologyKernelQuotient.{0,0,0} (ZMod 2)
      (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv.toLinearMap

private noncomputable def edge_scalarCycle (a : ZMod 2) :
    simplicialCycles edgeK (ZMod 2) 0 :=
  ⟨Finsupp.single (edge_vertex 0) a, by rw [simplicialCycles_zero]; trivial⟩

private noncomputable def edge_class (z : simplicialCycles edgeK (ZMod 2) 0) :=
  (simplicialBoundaries edgeK (ZMod 2) 0).mkQ z

set_option backward.isDefEq.respectTransparency false in
private theorem edge_quotSum_mkQ (z : simplicialCycles edgeK (ZMod 2) 0) :
    edge_quotSum (edge_class z) =
      edge_cycleSum z := rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem edge_normalization_boundary (z : simplicialCycles edgeK (ZMod 2) 0) :
    z - edge_scalarCycle (edge_cycleSum z) ∈
      simplicialBoundaries edgeK (ZMod 2) 0 := by
  apply (mem_simplicialBoundaries_iff (ZMod 2) edgeK 0 _).2
  refine ⟨Finsupp.single edge_face ((z : Chain edgeK (ZMod 2) 0) (edge_vertex 1)), ?_⟩
  change boundary edgeK (ZMod 2) 0
      (Finsupp.single edge_face ((z : Chain edgeK (ZMod 2) 0) (edge_vertex 1))) =
    (z : Chain edgeK (ZMod 2) 0) -
      Finsupp.single (edge_vertex 0) (edge_coeffSum (z : Chain edgeK (ZMod 2) 0))
  exact (edge_chain_decompose (z : Chain edgeK (ZMod 2) 0)).symm

private theorem quotient_class_eq {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) (x y : M) (h : x - y ∈ p) : p.mkQ x = p.mkQ y :=
  (Submodule.Quotient.eq p).mpr h

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem edge_quotient_normalization (z : simplicialCycles edgeK (ZMod 2) 0) :
    edge_class z = edge_class (edge_scalarCycle (edge_cycleSum z)) := by
  simpa only [edge_class] using
    quotient_class_eq (simplicialBoundaries edgeK (ZMod 2) 0) z
      (edge_scalarCycle (edge_cycleSum z)) (edge_normalization_boundary z)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem edge_H0_normalization (x : simplicialHomology edgeK (ZMod 2) 0) :
    x = (homologyKernelQuotient.{0,0,0} (ZMod 2)
      (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv.symm
        (edge_class
          (edge_scalarCycle (edge_H0_sum x))) := by
  let e := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv
  change x = e.symm (edge_class
    (edge_scalarCycle (edge_quotSum (e x))))
  apply e.injective
  rw [e.apply_symm_apply]
  refine Quotient.inductionOn (e x) ?_
  intro z
  change edge_class z =
    edge_class
      (edge_scalarCycle (edge_quotSum (edge_class z)))
  rw [edge_quotSum_mkQ]
  exact edge_quotient_normalization z

private theorem edge_H0_sum_vertex :
    ∃ x : simplicialHomology edgeK (ZMod 2) 0, edge_H0_sum x = 1 := by
  let e := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv
  let q := (simplicialBoundaries edgeK (ZMod 2) 0).mkQ edge_vertex0_cycle
  have hq : edge_quotSum q = 1 := by
    change edge_cycleSum edge_vertex0_cycle = 1
    change edge_coeffSum (Finsupp.single (edge_vertex 0) 1) = 1
    exact edge_coeffSum_single 0 1
  obtain ⟨x, hx⟩ := e.surjective q
  refine ⟨x, ?_⟩
  change edge_quotSum (e x) = 1
  rw [hx]
  exact hq

set_option backward.isDefEq.respectTransparency false in
private noncomputable def edge_H0Equiv :
    simplicialHomology edgeK (ZMod 2) 0 ≃ₗ[ZMod 2] ZMod 2 := by
  let e := (homologyKernelQuotient.{0,0,0} (ZMod 2)
    (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv
  have hs : Function.Surjective edge_H0_sum := by
    intro a
    refine ⟨e.symm (edge_class (edge_scalarCycle a)), ?_⟩
    change edge_quotSum (e (e.symm
      (edge_class (edge_scalarCycle a)))) = a
    rw [e.apply_symm_apply, edge_quotSum_mkQ]
    exact edge_coeffSum_single 0 a
  have hi : Function.Injective edge_H0_sum := by
    intro x y h
    calc
      x = e.symm (edge_class
          (edge_scalarCycle (edge_H0_sum x))) := edge_H0_normalization x
      _ = e.symm (edge_class
          (edge_scalarCycle (edge_H0_sum y))) := by rw [h]
      _ = y := (edge_H0_normalization y).symm
  exact LinearEquiv.ofBijective edge_H0_sum ⟨hi, hs⟩

set_option backward.isDefEq.respectTransparency false in
private theorem edge_H0Equiv_symm (a : ZMod 2) :
    edge_H0Equiv.symm a =
      (homologyKernelQuotient.{0,0,0} (ZMod 2)
        (simplicialChainComplex edgeK (ZMod 2)) 0).toLinearEquiv.symm
          (edge_class (edge_scalarCycle a)) := by
  have h : edge_H0_sum (edge_H0Equiv.symm a) = a := edge_H0Equiv.apply_symm_apply a
  simpa only [h] using edge_H0_normalization (edge_H0Equiv.symm a)

private theorem edge_scalar_generator_ne_zero
    {M N : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (e : M ≃ₗ[ZMod 2] ZMod 2) (f : M →ₗ[ZMod 2] N) (hf : f ≠ 0) :
    f (e.symm 1) ≠ 0 := by
  intro hz
  apply hf
  apply LinearMap.ext
  intro y
  have hy : y = (e y) • e.symm 1 := by
    apply e.injective
    simp
  rw [hy, map_smul, hz, smul_zero]
  simp

private theorem edge_two_full_pair_coordinates (a b : ZMod 2) :
    edge_H0Equiv
      ((simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom
        (edgeTwoPairEquiv.symm (a, b))) = a + b := by
  let g : ZMod 2 × ZMod 2 →ₗ[ZMod 2] ZMod 2 :=
    edge_H0Equiv.toLinearMap.comp
      ((simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom.comp
        edgeTwoPairEquiv.symm.toLinearMap)
  have h0 : g (1, 0) = 1 := by
    let x := edgeOneScalarEquiv.symm 1
    have hp := edge_first_two_pair_coordinates 1
    have hy : edgeTwoPairEquiv.symm (1, 0) =
        (simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom x := by
      apply edgeTwoPairEquiv.injective
      simpa [x] using hp.symm
    have hc := congrArg (fun f => f.hom x) edge_map_comp
    change (simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom x =
      (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom
        ((simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom x) at hc
    have hn : edge_H0Equiv
        ((simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom x) ≠ 0 := by
      intro hz
      exact (edge_scalar_generator_ne_zero edgeOneScalarEquiv
        (simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom
        edge_singleton_map_nonzero)
          (edge_H0Equiv.injective (hz.trans (map_zero _).symm))
    change edge_H0Equiv
      ((simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom
        (edgeTwoPairEquiv.symm (1, 0))) = 1
    rw [hy, ← hc]
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact (h _).resolve_left hn
  have h1 : g (0, 1) = 1 := by
    let x := edgeOtherScalarEquiv.symm 1
    have hp := edge_other_two_pair_coordinates 1
    have hy : edgeTwoPairEquiv.symm (0, 1) =
        (simplicialHomologyIncl (ZMod 2) edge_other_two 0).hom x := by
      apply edgeTwoPairEquiv.injective
      simpa [x] using hp.symm
    have hc := simplicialHomologyIncl_comp (ZMod 2) edge_other_two edge_two_le 0
    have hp' : edge_other_two.trans edge_two_le = edge_other_le :=
      Subsingleton.elim _ _
    rw [hp'] at hc
    have hh := congrArg (fun f => f.hom x) hc
    change (simplicialHomologyIncl (ZMod 2) edge_other_le 0).hom x =
      (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom
        ((simplicialHomologyIncl (ZMod 2) edge_other_two 0).hom x) at hh
    have hn : edge_H0Equiv
        ((simplicialHomologyIncl (ZMod 2) edge_other_le 0).hom x) ≠ 0 := by
      intro hz
      exact (edge_scalar_generator_ne_zero edgeOtherScalarEquiv
        (simplicialHomologyIncl (ZMod 2) edge_other_le 0).hom
        edge_other_map_nonzero)
          (edge_H0Equiv.injective (hz.trans (map_zero _).symm))
    change edge_H0Equiv
      ((simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom
        (edgeTwoPairEquiv.symm (0, 1))) = 1
    rw [hy, ← hh]
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact (h _).resolve_left hn
  have hp : (a, b) = a • (1, 0) + b • (0, 1) := by ext <;> simp
  change g (a, b) = a + b
  rw [hp, map_add, map_smul, map_smul, h0, h1]
  simp

private theorem edge_first_full_coordinates (a : ZMod 2) :
    edge_H0Equiv
      ((simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom
        (edgeOneScalarEquiv.symm a)) = a := by
  let x := edgeOneScalarEquiv.symm a
  let y := (simplicialHomologyIncl (ZMod 2) edge_singleton_two 0).hom x
  have hy : y = edgeTwoPairEquiv.symm (a, 0) := by
    apply edgeTwoPairEquiv.injective
    exact (edge_first_two_pair_coordinates a).trans
      (edgeTwoPairEquiv.apply_symm_apply (a, 0)).symm
  have hc := congrArg (fun f => f.hom x) edge_map_comp
  change (simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom x =
    (simplicialHomologyIncl (ZMod 2) edge_two_le 0).hom y at hc
  change edge_H0Equiv
    ((simplicialHomologyIncl (ZMod 2) edge_singleton_le 0).hom x) = a
  rw [hc, hy, edge_two_full_pair_coordinates]
  simp

end TDA.Persistence.Examples
