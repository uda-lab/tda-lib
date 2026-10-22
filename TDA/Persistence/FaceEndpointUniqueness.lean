import TDA.Persistence.FaceOrderTemplate
import TDA.Simplicial.Attachment

/-!
# Endpoint events in a fixed face order

The counts here are occurrence counts in the canonical rank barcode.  In
particular, a terminal death is not a face event.
-/

set_option autoImplicit false

universe u w
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration CategoryTheory

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {α : Type w} [LinearOrder α]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TotalFace K)]
variable {f : FilterFunction K α}

/-- The number of barcode intervals born when face `i` enters. -/
noncomputable def faceBirthCount (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) : ℕ :=
  (facePrefixBarcode k e n).countP (fun I => I.birth = i.val + 1)

/-- The number of barcode intervals dying when face `i` enters. -/
noncomputable def faceDeathCount (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) : ℕ :=
  (facePrefixBarcode k e n).countP (fun I => I.death = i.val + 1)

private theorem birth_partition {N : ℕ} (B : Multiset (FiniteInterval N))
    (a b : Fin N) (hab : b.val = a.val + 1) :
    B.countP (fun I => I.birth = b.val) +
      B.countP (fun I => I.birth ≤ a.val ∧ b.val < I.death) =
      B.countP (fun I => I.birth ≤ b.val ∧ b.val < I.death) := by
  classical
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons I B ih =>
    simp only [Multiset.countP_cons]
    rw [← ih]
    have hI := I.birth_lt_death
    split_ifs <;> omega

private theorem death_partition {N : ℕ} (B : Multiset (FiniteInterval N))
    (a b : Fin N) (hab : b.val = a.val + 1) :
    B.countP (fun I => I.death = b.val) +
      B.countP (fun I => I.birth ≤ a.val ∧ b.val < I.death) =
      B.countP (fun I => I.birth ≤ a.val ∧ a.val < I.death) := by
  classical
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons I B ih =>
    simp only [Multiset.countP_cons]
    rw [← ih]
    have hI := I.birth_lt_death
    split_ifs <;> omega

private theorem prefix_rank_eq_count (e : CompatibleOrder f) (n : ℕ)
    (a b : Fin (faceCount K + 1)) (hab : a ≤ b) :
    structureMapRank (facePrefixModule k e n) a b hab =
      (facePrefixBarcode k e n).countP
        (fun I => I.birth ≤ a.val ∧ b.val < I.death) := by
  rw [← rank_barcodeMap (k := k) (facePrefixBarcode k e n) a b hab]
  exact (structureMapRank_rankBarcode (facePrefixModule k e n) a b hab).symm

/-- Adjacent ranks count births as the dimension gained beyond the image. -/
theorem faceBirthCount_add_rank (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) :
    faceBirthCount k e n i +
      structureMapRank (facePrefixModule k e n)
        ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        (Fin.le_def.mpr (Nat.le_succ _)) =
      Module.finrank k ((facePrefixModule k e n).obj
        ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) := by
  let a : Fin (faceCount K + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let b : Fin (faceCount K + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  have hab : a ≤ b := by apply Fin.le_def.mpr; dsimp [a, b]; omega
  have hp := birth_partition (facePrefixBarcode k e n) a b (by rfl)
  have hself : structureMapRank (facePrefixModule k e n) b b le_rfl =
      Module.finrank k ((facePrefixModule k e n).obj b) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id]
    simp
  rw [← hself, prefix_rank_eq_count k e n a b hab,
    prefix_rank_eq_count k e n b b le_rfl]
  exact hp

/-- Adjacent ranks count deaths as the dimension lost into the kernel. -/
theorem faceDeathCount_add_rank (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) :
    faceDeathCount k e n i +
      structureMapRank (facePrefixModule k e n)
        ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        (Fin.le_def.mpr (Nat.le_succ _)) =
      Module.finrank k ((facePrefixModule k e n).obj
        ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
  let a : Fin (faceCount K + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let b : Fin (faceCount K + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  have hab : a ≤ b := by apply Fin.le_def.mpr; dsimp [a, b]; omega
  have hp := death_partition (facePrefixBarcode k e n) a b (by rfl)
  have hself : structureMapRank (facePrefixModule k e n) a a le_rfl =
      Module.finrank k ((facePrefixModule k e n).obj a) := by
    unfold structureMapRank
    rw [structureMapLinear_self, LinearMap.range_id]
    simp
  rw [← hself, prefix_rank_eq_count k e n a b hab,
    prefix_rank_eq_count k e n a a le_rfl]
  exact hp

/-- The birth count is the adjacent-map cokernel dimension. -/
theorem faceBirthCount_eq_cokernel (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) :
    faceBirthCount k e n i =
      Module.finrank k (((facePrefixModule k e n).obj
        ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ⧸
        LinearMap.range (structureMapLinear (facePrefixModule k e n)
          (Fin.le_def.mpr (Nat.le_succ _) :
            (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (faceCount K + 1)) ≤
              ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))) := by
  let a : Fin (faceCount K + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let b : Fin (faceCount K + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let h : a ≤ b := Fin.le_def.mpr (Nat.le_succ _)
  have hr := faceBirthCount_add_rank k e n i
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (structureMapLinear (facePrefixModule k e n) h))
  change faceBirthCount k e n i +
    Module.finrank k (LinearMap.range (structureMapLinear (facePrefixModule k e n) h)) =
      Module.finrank k ((facePrefixModule k e n).obj b) at hr
  change Module.finrank k (((facePrefixModule k e n).obj b) ⧸
      LinearMap.range (structureMapLinear (facePrefixModule k e n) h)) +
    Module.finrank k (LinearMap.range (structureMapLinear (facePrefixModule k e n) h)) =
      Module.finrank k ((facePrefixModule k e n).obj b) at hq
  exact Nat.add_right_cancel (hr.trans hq.symm)

/-- The death count is the adjacent-map kernel dimension. -/
theorem faceDeathCount_eq_kernel (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) :
    faceDeathCount k e n i =
      Module.finrank k (LinearMap.ker (structureMapLinear (facePrefixModule k e n)
        (Fin.le_def.mpr (Nat.le_succ _) :
          (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (faceCount K + 1)) ≤
            ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))) := by
  let a : Fin (faceCount K + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let b : Fin (faceCount K + 1) := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let h : a ≤ b := Fin.le_def.mpr (Nat.le_succ _)
  have hr := faceDeathCount_add_rank k e n i
  have hk := LinearMap.finrank_range_add_finrank_ker
    (structureMapLinear (facePrefixModule k e n) h)
  change faceDeathCount k e n i +
    Module.finrank k (LinearMap.range (structureMapLinear (facePrefixModule k e n) h)) =
      Module.finrank k ((facePrefixModule k e n).obj a) at hr
  change Module.finrank k (LinearMap.range (structureMapLinear (facePrefixModule k e n) h)) +
      Module.finrank k (LinearMap.ker (structureMapLinear (facePrefixModule k e n) h)) =
        Module.finrank k ((facePrefixModule k e n).obj a) at hk
  change faceDeathCount k e n i =
    Module.finrank k (LinearMap.ker (structureMapLinear (facePrefixModule k e n) h))
  omega

/-- Consecutive compatible prefixes differ by exactly the enumerated face. -/
def faceStepAttachment (e : CompatibleOrder f) (i : Fin (faceCount K)) :
    SimplexAttachment (e.prefixComplex i.val) (e.prefixComplex (i.val + 1))
      ((e.enum i).val.card - 1) where
  simplex := (e.enum i).val
  card_simplex := by
    have hne := (K.isRelLowerSet_faces (e.enum i).property).1
    have hp : 0 < (e.enum i).val.card := Finset.card_pos.mpr hne
    omega
  not_mem := by
    intro hs
    obtain ⟨_, hi⟩ := (e.mem_prefixComplex i.val _).mp hs
    have he : e.enum.symm (e.enum i) = i := e.enum.symm_apply_apply i
    rw [he] at hi
    exact (Nat.lt_irrefl _) hi
  face_iff := by
    intro s
    constructor
    · intro hs
      obtain ⟨hsK, hi⟩ := (e.mem_prefixComplex (i.val + 1) s).mp hs
      by_cases hlt : (e.enum.symm ⟨s, hsK⟩).val < i.val
      · exact Or.inl ((e.mem_prefixComplex i.val s).mpr ⟨hsK, hlt⟩)
      · right
        have heq : (e.enum.symm ⟨s, hsK⟩).val = i.val := by omega
        have hfin : e.enum.symm ⟨s, hsK⟩ = i := Fin.ext heq
        have hface : (⟨s, hsK⟩ : TotalFace K) = e.enum i := by
          rw [← e.enum.apply_symm_apply ⟨s, hsK⟩, hfin]
        exact congrArg Subtype.val hface
    · rintro (hs | rfl)
      · exact e.prefixComplex_mono (Nat.le_succ _) hs
      · apply (e.mem_prefixComplex (i.val + 1) _).mpr
        refine ⟨(e.enum i).property, ?_⟩
        rw [e.enum.symm_apply_apply]
        exact Nat.lt_succ_self _

private theorem faceStep_map_eq (e : CompatibleOrder f) (i : Fin (faceCount K))
    (n : ℕ) :
    structureMapLinear (facePrefixModule k e n)
      (Fin.le_def.mpr (Nat.le_succ _) :
        (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (faceCount K + 1)) ≤
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) =
      (simplicialHomologyIncl k (faceStepAttachment e i).inclusion n).hom := by
  rfl

private theorem faceBirthCount_of_surjective (e : CompatibleOrder f)
    (i : Fin (faceCount K)) (n : ℕ)
    (h : Function.Surjective (simplicialHomologyIncl k
      (faceStepAttachment e i).inclusion n).hom) :
    faceBirthCount k e n i = 0 := by
  rw [faceBirthCount_eq_cokernel, faceStep_map_eq]
  change Module.finrank k (simplicialHomology (e.prefixComplex (i.val + 1)) k n ⧸
    LinearMap.range (simplicialHomologyIncl k (faceStepAttachment e i).inclusion n).hom) = 0
  rw [LinearMap.range_eq_top.mpr h]
  exact Module.finrank_zero_of_subsingleton (R := k)

private theorem faceDeathCount_of_injective (e : CompatibleOrder f)
    (i : Fin (faceCount K)) (n : ℕ)
    (h : Function.Injective (simplicialHomologyIncl k
      (faceStepAttachment e i).inclusion n).hom) :
    faceDeathCount k e n i = 0 := by
  rw [faceDeathCount_eq_kernel, faceStep_map_eq]
  change Module.finrank k (LinearMap.ker (simplicialHomologyIncl k
    (faceStepAttachment e i).inclusion n).hom) = 0
  rw [LinearMap.ker_eq_bot.mpr h]
  simp

private theorem faceBirthCount_of_cokernel_one (e : CompatibleOrder f)
    (i : Fin (faceCount K)) (n : ℕ)
    (h : Module.finrank k (simplicialHomology (e.prefixComplex (i.val + 1)) k n ⧸
      LinearMap.range (simplicialHomologyIncl k
        (faceStepAttachment e i).inclusion n).hom) = 1) :
    faceBirthCount k e n i = 1 := by
  rw [faceBirthCount_eq_cokernel, faceStep_map_eq]
  exact h

private theorem faceDeathCount_of_kernel_one (e : CompatibleOrder f)
    (i : Fin (faceCount K)) (n : ℕ)
    (h : Module.finrank k (LinearMap.ker (simplicialHomologyIncl k
      (faceStepAttachment e i).inclusion n).hom) = 1) :
    faceDeathCount k e n i = 1 := by
  rw [faceDeathCount_eq_kernel, faceStep_map_eq]
  exact h

/-- The attachment alternatives give one barcode event, in one degree, at each face. -/
theorem faceStep_unique_event (e : CompatibleOrder f) (i : Fin (faceCount K)) :
    ∃ q : ℕ,
      ((faceBirthCount k e q i = 1 ∧ faceDeathCount k e q i = 0 ∧
          ∀ r : ℕ, r ≠ q →
            faceBirthCount k e r i = 0 ∧ faceDeathCount k e r i = 0) ∨
       (faceBirthCount k e q i = 0 ∧ faceDeathCount k e q i = 1 ∧
          ∀ r : ℕ, r ≠ q →
            faceBirthCount k e r i = 0 ∧ faceDeathCount k e r i = 0)) := by
  let A := faceStepAttachment e i
  letI : Finite (TotalFace (e.prefixComplex (i.val + 1))) :=
    Finite.of_injective
      (fun s => (⟨s.1, ((e.mem_prefixComplex (i.val + 1) s.1).mp s.2).1⟩ : TotalFace K))
      (by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun t : TotalFace K => t.1) h)
  let q := (e.enum i).val.card - 1
  by_cases hq : q = 0
  · let A0 : SimplexAttachment (e.prefixComplex i.val)
        (e.prefixComplex (i.val + 1)) 0 := hq ▸ A
    obtain ⟨hinj, hcoker, hrest⟩ := A0.isolatedVertex_birth k
    refine ⟨0, Or.inl ⟨?_, ?_, ?_⟩⟩
    · exact faceBirthCount_of_cokernel_one k e i 0 hcoker
    · exact faceDeathCount_of_injective k e i 0 hinj
    · intro r hr
      obtain ⟨hrinj, hrsurj⟩ := hrest r (Nat.pos_of_ne_zero hr)
      exact ⟨faceBirthCount_of_surjective k e i r hrsurj,
        faceDeathCount_of_injective k e i r hrinj⟩
  · obtain ⟨p, hp⟩ : ∃ p : ℕ, q = p + 1 := by
      refine ⟨q - 1, ?_⟩
      omega
    let Ap : SimplexAttachment (e.prefixComplex i.val)
        (e.prefixComplex (i.val + 1)) (p + 1) := hp ▸ A
    by_cases hz : Ap.attachingHomologyClass k = 0
    · obtain ⟨hinj, hcoker, hrest, _⟩ := Ap.positive_birth k hz
      refine ⟨p + 1, Or.inl ⟨?_, ?_, ?_⟩⟩
      · exact faceBirthCount_of_cokernel_one k e i (p + 1) hcoker
      · exact faceDeathCount_of_injective k e i (p + 1) hinj
      · intro r hr
        obtain ⟨hrinj, hrsurj⟩ := hrest r hr
        exact ⟨faceBirthCount_of_surjective k e i r hrsurj,
          faceDeathCount_of_injective k e i r hrinj⟩
    · obtain ⟨hsurj, _, hker, hrest⟩ := Ap.positive_death k hz
      refine ⟨p, Or.inr ⟨?_, ?_, ?_⟩⟩
      · exact faceBirthCount_of_surjective k e i p hsurj
      · exact faceDeathCount_of_kernel_one k e i p hker
      · intro r hr
        obtain ⟨hrinj, hrsurj⟩ := hrest r hr
        exact ⟨faceBirthCount_of_surjective k e i r hrsurj,
          faceDeathCount_of_injective k e i r hrinj⟩

/-- Finite pair death endpoints are exactly barcode deaths at a face stage. -/
theorem faceTemplate_death_count (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) :
    (faceTemplatePairs k e n).countP (fun pair => pair.2 = i) =
      faceDeathCount k e n i := by
  classical
  unfold faceTemplatePairs faceDeathCount
  generalize hB : facePrefixBarcode k e n = B
  have hpos : ∀ I ∈ B, 0 < I.birth := by
    intro I hI
    exact facePrefixBarcode_birth_pos k e n I (hB.symm ▸ hI)
  clear hB
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons I B ih =>
    have hp : 0 < I.birth := hpos I (by simp)
    have hpB : ∀ J ∈ B, 0 < J.birth := by
      intro J hJ
      exact hpos J (by simp [hJ])
    simp only [Multiset.filterMap_cons]
    split_ifs with hb hd
    · simp only [Option.map_some, Option.getD_some,
        Multiset.singleton_add, Multiset.countP_cons]
      rw [ih hpB]
      simp only [Fin.ext_iff]
      change B.countP (fun I => I.death = i.val + 1) +
          (if I.death - 1 = i.val then 1 else 0) =
        B.countP (fun I => I.death = i.val + 1) +
          (if I.death = i.val + 1 then 1 else 0)
      have hI := I.birth_lt_death
      split_ifs <;> omega
    · simp only [Option.map_none, Option.getD_none, zero_add,
        Multiset.countP_cons]
      rw [ih hpB]
      have hneq : I.death ≠ i.val + 1 := by omega
      simp [hneq]

/-- Birth endpoints split into finite first endpoints and essential indices. -/
theorem faceTemplate_birth_count (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) :
    (faceTemplatePairs k e n).countP (fun pair => pair.1 = i) +
      (faceTemplateEssential k e n).count i = faceBirthCount k e n i := by
  classical
  unfold faceTemplatePairs faceTemplateEssential faceBirthCount
  generalize hB : facePrefixBarcode k e n = B
  have hpos : ∀ I ∈ B, 0 < I.birth := by
    intro I hI
    exact facePrefixBarcode_birth_pos k e n I (hB.symm ▸ hI)
  clear hB
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons I B ih =>
    have hp : 0 < I.birth := hpos I (by simp)
    have hpB : ∀ J ∈ B, 0 < J.birth := by
      intro J hJ
      exact hpos J (by simp [hJ])
    by_cases hd : I.death ≤ faceCount K
    · simp only [Multiset.filterMap_cons]
      simp only [dif_pos hp, dif_pos hd, if_pos hd,
        Option.map_some, Option.getD_some, Option.map_none,
        Option.getD_none, Multiset.singleton_add, zero_add,
        Multiset.countP_cons]
      have htail := ih hpB
      simp only [Fin.ext_iff]
      simp only [Fin.ext_iff] at htail
      have hI := I.birth_lt_death
      split_ifs with hidx hborn
      all_goals
        first
        | change I.birth - 1 = i.val at hidx
        | change I.birth - 1 ≠ i.val at hidx
        omega
    · simp only [Multiset.filterMap_cons]
      simp only [dif_pos hp, dif_neg hd, if_neg hd]
      simp only [Option.map_some, Option.getD_some, Option.map_none,
        Option.getD_none, Multiset.singleton_add, zero_add,
        Multiset.count_cons, Multiset.countP_cons]
      have htail := ih hpB
      simp only [Fin.ext_iff]
      simp only [Fin.ext_iff] at htail
      have hI := I.birth_lt_death
      split_ifs with hidx hborn
      all_goals
        first
        | change I.birth - 1 = i.val at hidx
        | change I.birth - 1 ≠ i.val at hidx
        | change i.val = I.birth - 1 at hidx
        | change i.val ≠ I.birth - 1 at hidx
        omega

/-- Each face contributes exactly one endpoint occurrence, jointly across degrees
and across finite births, finite deaths, and essential births. -/
theorem faceTemplate_unique_endpoint (e : CompatibleOrder f)
    (i : Fin (faceCount K)) :
    ∃ q : ℕ,
      (((faceTemplatePairs k e q).countP (fun pair => pair.1 = i) +
            (faceTemplateEssential k e q).count i = 1 ∧
          (faceTemplatePairs k e q).countP (fun pair => pair.2 = i) = 0 ∧
          ∀ r : ℕ, r ≠ q →
            (faceTemplatePairs k e r).countP (fun pair => pair.1 = i) +
                (faceTemplateEssential k e r).count i = 0 ∧
              (faceTemplatePairs k e r).countP (fun pair => pair.2 = i) = 0) ∨
       ((faceTemplatePairs k e q).countP (fun pair => pair.1 = i) +
            (faceTemplateEssential k e q).count i = 0 ∧
          (faceTemplatePairs k e q).countP (fun pair => pair.2 = i) = 1 ∧
          ∀ r : ℕ, r ≠ q →
            (faceTemplatePairs k e r).countP (fun pair => pair.1 = i) +
                (faceTemplateEssential k e r).count i = 0 ∧
              (faceTemplatePairs k e r).countP (fun pair => pair.2 = i) = 0)) := by
  simpa only [faceTemplate_birth_count, faceTemplate_death_count] using
    faceStep_unique_event k e i

/-- In one degree, no face can occupy two endpoint roles. -/
theorem faceTemplate_endpoint_count_le_one (e : CompatibleOrder f)
    (i : Fin (faceCount K)) (n : ℕ) :
    (faceTemplatePairs k e n).countP (fun pair => pair.1 = i) +
      (faceTemplateEssential k e n).count i +
      (faceTemplatePairs k e n).countP (fun pair => pair.2 = i) ≤ 1 := by
  obtain ⟨q, h⟩ := faceTemplate_unique_endpoint k e i
  rcases h with ⟨hb, hd, hother⟩ | ⟨hb, hd, hother⟩
  · by_cases hn : n = q
    · subst n; omega
    · obtain ⟨hz, hz'⟩ := hother n hn
      omega
  · by_cases hn : n = q
    · subst n; omega
    · obtain ⟨hz, hz'⟩ := hother n hn
      omega

/-- Different degrees cannot use the same face as an endpoint. -/
theorem faceTemplate_endpoint_degrees_disjoint (e : CompatibleOrder f)
    (i : Fin (faceCount K)) (n r : ℕ) (hnr : n ≠ r)
    (hn : 0 < (faceTemplatePairs k e n).countP (fun pair => pair.1 = i) +
      (faceTemplateEssential k e n).count i +
      (faceTemplatePairs k e n).countP (fun pair => pair.2 = i)) :
    (faceTemplatePairs k e r).countP (fun pair => pair.1 = i) +
      (faceTemplateEssential k e r).count i +
      (faceTemplatePairs k e r).countP (fun pair => pair.2 = i) = 0 := by
  obtain ⟨q, h⟩ := faceTemplate_unique_endpoint k e i
  rcases h with ⟨hb, hd, hother⟩ | ⟨hb, hd, hother⟩
  · have hnq : n = q := by
      by_contra hne
      obtain ⟨hz, hz'⟩ := hother n hne
      omega
    obtain ⟨hz, hz'⟩ := hother r (by omega)
    omega
  · have hnq : n = q := by
      by_contra hne
      obtain ⟨hz, hz'⟩ := hother n hne
      omega
    obtain ⟨hz, hz'⟩ := hother r (by omega)
    omega

private theorem multiset_count_le_countP {X : Type*} [DecidableEq X]
    (s : Multiset X) (x : X) (p : X → Prop) [DecidablePred p]
    (hx : p x) : s.count x ≤ s.countP p := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons y s ih =>
    simp only [Multiset.count_cons, Multiset.countP_cons]
    split_ifs with h₁ h₂ <;> simp_all <;> omega

/-- A finite template pair cannot appear twice as an indexed occurrence. -/
theorem faceTemplatePairs_count_le_one (e : CompatibleOrder f) (n : ℕ)
    (pair : Fin (faceCount K) × Fin (faceCount K)) :
    (faceTemplatePairs k e n).count pair ≤ 1 := by
  have hbound := faceTemplate_endpoint_count_le_one k e pair.1 n
  have hle := multiset_count_le_countP (faceTemplatePairs k e n) pair
    (fun x => x.1 = pair.1) rfl
  omega

/-- An essential birth index cannot appear twice. -/
theorem faceTemplateEssential_count_le_one (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) :
    (faceTemplateEssential k e n).count i ≤ 1 := by
  have hbound := faceTemplate_endpoint_count_le_one k e i n
  omega

/-- A face can contribute a finite death in degree `n` only when it has `n+2` vertices. -/
theorem faceDeathCount_eq_zero_of_card_ne (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) (h : (e.enum i).val.card ≠ n + 2) :
    faceDeathCount k e n i = 0 := by
  let A := faceStepAttachment e i
  letI : Finite (TotalFace (e.prefixComplex (i.val + 1))) :=
    Finite.of_injective
      (fun s => (⟨s.1, ((e.mem_prefixComplex (i.val + 1) s.1).mp s.2).1⟩ : TotalFace K))
      (by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun t : TotalFace K => t.1) hxy)
  let q := (e.enum i).val.card - 1
  have hq_def : q = (e.enum i).val.card - 1 := rfl
  have hpos : 0 < (e.enum i).val.card :=
    Finset.card_pos.mpr (K.isRelLowerSet_faces (e.enum i).property).1
  by_cases hq : q = 0
  · let A0 : SimplexAttachment (e.prefixComplex i.val)
        (e.prefixComplex (i.val + 1)) 0 := hq ▸ A
    obtain ⟨hinj, _, hrest⟩ := A0.isolatedVertex_birth k
    by_cases hn : n = 0
    · subst n
      exact faceDeathCount_of_injective k e i 0 hinj
    · obtain ⟨hrinj, _⟩ := hrest n (Nat.pos_of_ne_zero hn)
      exact faceDeathCount_of_injective k e i n hrinj
  · obtain ⟨p, hp⟩ : ∃ p : ℕ, q = p + 1 := by
      refine ⟨q - 1, ?_⟩
      omega
    let Ap : SimplexAttachment (e.prefixComplex i.val)
        (e.prefixComplex (i.val + 1)) (p + 1) := hp ▸ A
    by_cases hz : Ap.attachingHomologyClass k = 0
    · obtain ⟨hinj, _, hrest, _⟩ := Ap.positive_birth k hz
      by_cases hn : n = p + 1
      · obtain rfl := hn
        exact faceDeathCount_of_injective k e i (p + 1) hinj
      · obtain ⟨hrinj, _⟩ := hrest n hn
        exact faceDeathCount_of_injective k e i n hrinj
    · obtain ⟨_, _, hker, hrest⟩ := Ap.positive_death k hz
      by_cases hn : n = p
      · exfalso
        obtain rfl := hn
        apply h
        omega
      · obtain ⟨hrinj, _⟩ := hrest n hn
        exact faceDeathCount_of_injective k e i n hrinj

/-- A face can contribute a birth in degree `n` only when it has `n+1` vertices. -/
theorem faceBirthCount_eq_zero_of_card_ne (e : CompatibleOrder f) (n : ℕ)
    (i : Fin (faceCount K)) (h : (e.enum i).val.card ≠ n + 1) :
    faceBirthCount k e n i = 0 := by
  let A := faceStepAttachment e i
  letI : Finite (TotalFace (e.prefixComplex (i.val + 1))) :=
    Finite.of_injective
      (fun s => (⟨s.1, ((e.mem_prefixComplex (i.val + 1) s.1).mp s.2).1⟩ : TotalFace K))
      (by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun t : TotalFace K => t.1) hxy)
  let q := (e.enum i).val.card - 1
  have hq_def : q = (e.enum i).val.card - 1 := rfl
  have hpos : 0 < (e.enum i).val.card :=
    Finset.card_pos.mpr (K.isRelLowerSet_faces (e.enum i).property).1
  by_cases hq : q = 0
  · let A0 : SimplexAttachment (e.prefixComplex i.val)
        (e.prefixComplex (i.val + 1)) 0 := hq ▸ A
    obtain ⟨_, hcoker, hrest⟩ := A0.isolatedVertex_birth k
    by_cases hn : n = 0
    · exfalso
      obtain rfl := hn
      apply h
      omega
    · obtain ⟨_, hrsurj⟩ := hrest n (Nat.pos_of_ne_zero hn)
      exact faceBirthCount_of_surjective k e i n hrsurj
  · obtain ⟨p, hp⟩ : ∃ p : ℕ, q = p + 1 := by
      refine ⟨q - 1, ?_⟩
      omega
    let Ap : SimplexAttachment (e.prefixComplex i.val)
        (e.prefixComplex (i.val + 1)) (p + 1) := hp ▸ A
    by_cases hz : Ap.attachingHomologyClass k = 0
    · obtain ⟨_, hcoker, hrest, _⟩ := Ap.positive_birth k hz
      by_cases hn : n = p + 1
      · exfalso
        obtain rfl := hn
        apply h
        omega
      · obtain ⟨_, hrsurj⟩ := hrest n hn
        exact faceBirthCount_of_surjective k e i n hrsurj
    · obtain ⟨hsurj, _, _, hrest⟩ := Ap.positive_death k hz
      by_cases hn : n = p
      · obtain rfl := hn
        exact faceBirthCount_of_surjective k e i _ hsurj
      · obtain ⟨_, hrsurj⟩ := hrest n hn
        exact faceBirthCount_of_surjective k e i n hrsurj

end TDA.Persistence
