import TDA.Persistence.FiniteDecomposition
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Same-birth survival counts under epimorphisms

At a positive birth, count the image at a later stage modulo the preceding image.
At birth zero there is no preceding stage, so use the image itself. Naturality and
component surjectivity supply actual surjections before dimensions are compared.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory

variable {s : ℕ}

/-- Count occurrences born exactly at `b` and still alive at the observed stage `c`. -/
def birthSuffixCount (B : Multiset (FiniteInterval s)) (b c : ℕ) : ℕ := by
  classical
  exact B.countP (fun I => I.birth = b ∧ c < I.death)

private theorem count_birth_step (B : Multiset (FiniteInterval s)) (b c : ℕ)
    (hb : 0 < b) :
    B.countP (fun I => I.birth ≤ b ∧ c < I.death) =
      birthSuffixCount B b c + B.countP (fun I => I.birth ≤ b - 1 ∧ c < I.death) := by
  classical
  induction B using Multiset.induction_on with
  | empty => simp [birthSuffixCount]
  | @cons I B ih =>
    simp only [birthSuffixCount, Multiset.countP_cons] at ih ⊢
    split_ifs <;> omega

variable {k : Type u} [Field k]

/-- The preceding image as a submodule of the image from the birth stage.
The bounds justify the predecessor and every finite index. -/
def birthPreviousImage (M : PModule.{u,0,u} k (Fin s)) (b c : ℕ)
    (hb : 0 < b) (hbc : b ≤ c) (hc : c < s) :
    Submodule k (LinearMap.range (structureMapLinear M
      (show (⟨b, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc))) :=
  (LinearMap.range (structureMapLinear M
    (show (⟨b - 1, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from by change b - 1 ≤ c; omega))).comap
      (LinearMap.range (structureMapLinear M
        (show (⟨b, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc))).subtype

private theorem previous_image_le (M : PModule.{u,0,u} k (Fin s)) (b c : ℕ)
    (hb : 0 < b) (hbc : b ≤ c) (hc : c < s) :
    LinearMap.range (structureMapLinear M
      (show (⟨b - 1, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from by change b - 1 ≤ c; omega)) ≤
    LinearMap.range (structureMapLinear M
      (show (⟨b, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc)) := by
  rw [structureMapLinear_comp M
    (show (⟨b - 1, by omega⟩ : Fin s) ≤ ⟨b, by omega⟩ from by change b - 1 ≤ b; omega)
    (show (⟨b, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc)]
  exact LinearMap.range_comp_le_range _ _

private theorem previous_image_finrank (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] (b c : ℕ)
    (hb : 0 < b) (hbc : b ≤ c) (hc : c < s) :
    Module.finrank k (birthPreviousImage M b c hb hbc hc) =
      structureMapRank M ⟨b - 1, by omega⟩ ⟨c, hc⟩ (by change b - 1 ≤ c; omega) := by
  unfold birthPreviousImage structureMapRank
  rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
    inf_of_le_right (previous_image_le M b c hb hbc hc)]

/-- For a positive birth, the survival count is the dimension of the actual
image quotient. The preceding image lies inside the current one by composition. -/
theorem birthSuffixCount_eq_finrank (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] (b c : ℕ)
    (hb : 0 < b) (hbc : b ≤ c) (hc : c < s) :
    birthSuffixCount (rankBarcode M) b c =
      Module.finrank k ((LinearMap.range (structureMapLinear M
        (show (⟨b, Nat.lt_of_le_of_lt hbc hc⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc))) ⧸
          birthPreviousImage M b c hb hbc hc) := by
  have hcounts := count_birth_step (rankBarcode M) b c hb
  have hcurrent := structureMapRank_rankBarcode M ⟨b, by omega⟩ ⟨c, hc⟩ hbc
  have hprevious := structureMapRank_rankBarcode M ⟨b - 1, by omega⟩ ⟨c, hc⟩
    (by change b - 1 ≤ c; omega)
  rw [rank_barcodeMap] at hcurrent hprevious
  have hdim := (birthPreviousImage M b c hb hbc hc).finrank_quotient_add_finrank
  rw [previous_image_finrank] at hdim
  change _ + _ = structureMapRank M ⟨b, by omega⟩ ⟨c, hc⟩ hbc at hdim
  change (rankBarcode M).countP (fun I => I.birth ≤ b ∧ c < I.death) = _ at hcurrent
  change (rankBarcode M).countP (fun I => I.birth ≤ b - 1 ∧ c < I.death) = _ at hprevious
  omega

/-- Birth zero uses the first image; it never selects a preceding stage. -/
theorem birthSuffixCount_zero (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] (c : ℕ) (hc : c < s) :
    birthSuffixCount (rankBarcode M) 0 c =
      structureMapRank M ⟨0, by omega⟩ ⟨c, hc⟩ (by change 0 ≤ c; omega) := by
  have h := structureMapRank_rankBarcode M ⟨0, by omega⟩ ⟨c, hc⟩
    (by change 0 ≤ c; omega)
  rw [rank_barcodeMap] at h
  simpa [birthSuffixCount, Nat.le_zero] using h

private theorem naturality_apply {M N : PModule.{u,0,u} k (Fin s)} (p : M ⟶ N)
    {a c : Fin s} (h : a ≤ c) (x : M.obj a) :
    (p.app c).hom (structureMapLinear M h x) =
      structureMapLinear N h ((p.app a).hom x) :=
  congrArg (fun f : M.obj a ⟶ N.obj c => f.hom x) (p.naturality (homOfLE h))

private def imageMap {M N : PModule.{u,0,u} k (Fin s)} (p : M ⟶ N)
    {a c : Fin s} (h : a ≤ c) :
    LinearMap.range (structureMapLinear M h) →ₗ[k] LinearMap.range (structureMapLinear N h) :=
  ((p.app c).hom.comp (LinearMap.range (structureMapLinear M h)).subtype).codRestrict _ (by
    rintro ⟨x, y, rfl⟩
    exact ⟨(p.app a).hom y, (naturality_apply p h y).symm⟩)

private theorem imageMap_surjective {M N : PModule.{u,0,u} k (Fin s)} (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom) {a c : Fin s} (h : a ≤ c) :
    Function.Surjective (imageMap p h) := by
  rintro ⟨y, x, rfl⟩
  obtain ⟨z, rfl⟩ := hp a x
  refine ⟨⟨structureMapLinear M h z, z, rfl⟩, ?_⟩
  apply Subtype.ext
  exact naturality_apply p h z

private theorem imageMap_previous {M N : PModule.{u,0,u} k (Fin s)} (p : M ⟶ N)
    (b c : ℕ) (hb : 0 < b) (hbc : b ≤ c) (hc : c < s) :
    birthPreviousImage M b c hb hbc hc ≤
      (birthPreviousImage N b c hb hbc hc).comap
        (imageMap p (show (⟨b, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc)) := by
  rintro x ⟨y, hy⟩
  change (p.app _).hom x.val ∈ LinearMap.range (structureMapLinear N _)
  refine ⟨(p.app ⟨b - 1, by omega⟩).hom y, ?_⟩
  rw [← naturality_apply, hy]
  rfl

private def birthQuotientMap {M N : PModule.{u,0,u} k (Fin s)} (p : M ⟶ N)
    (b c : ℕ) (hb : 0 < b) (hbc : b ≤ c) (hc : c < s) :
    ((LinearMap.range (structureMapLinear M
      (show (⟨b, Nat.lt_of_le_of_lt hbc hc⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc))) ⧸ birthPreviousImage M b c hb hbc hc) →ₗ[k]
    ((LinearMap.range (structureMapLinear N
      (show (⟨b, Nat.lt_of_le_of_lt hbc hc⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc))) ⧸ birthPreviousImage N b c hb hbc hc) :=
  (birthPreviousImage M b c hb hbc hc).mapQ (birthPreviousImage N b c hb hbc hc)
    (imageMap p _) (imageMap_previous p b c hb hbc hc)

private theorem birthQuotientMap_surjective {M N : PModule.{u,0,u} k (Fin s)} (p : M ⟶ N)
    (hp : ∀ i, Function.Surjective (p.app i).hom)
    (b c : ℕ) (hb : 0 < b) (hbc : b ≤ c) (hc : c < s) :
    Function.Surjective (birthQuotientMap p b c hb hbc hc) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨x, rfl⟩ := imageMap_surjective p hp
      (show (⟨b, by omega⟩ : Fin s) ≤ ⟨c, hc⟩ from hbc) y
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- A componentwise surjection decreases the same-birth survival counts.
The proof compares actual image quotient surjections, with birth zero handled separately. -/
theorem birthSuffixCount_le_of_surjective {M N : PModule.{u,0,u} k (Fin s)}
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]
    (p : M ⟶ N) (hp : ∀ i, Function.Surjective (p.app i).hom)
    (b c : ℕ) (hbc : b ≤ c) (hc : c < s) :
    birthSuffixCount (rankBarcode N) b c ≤ birthSuffixCount (rankBarcode M) b c := by
  by_cases hb : b = 0
  · subst b
    rw [birthSuffixCount_zero M c hc, birthSuffixCount_zero N c hc]
    exact LinearMap.finrank_le_finrank_of_surjective (imageMap_surjective p hp _)
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    rw [birthSuffixCount_eq_finrank M b c hbpos hbc hc,
      birthSuffixCount_eq_finrank N b c hbpos hbc hc]
    exact LinearMap.finrank_le_finrank_of_surjective
      (birthQuotientMap_surjective p hp b c hbpos hbc hc)

end TDA.Persistence.FiniteBarcode
