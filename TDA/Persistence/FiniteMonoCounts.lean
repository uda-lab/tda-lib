import TDA.Persistence.FiniteDecomposition
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Same-death barcode counts under monomorphisms

For an observed death, count the image of an earlier structure map intersected with
the kernel of the next one. A terminal death instead uses the final image. Naturality
restricts a component injection to these actual subspaces, before dimensions are compared.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory

variable {s : ℕ}

/-- Count occurrences born by `b` with exactly the specified observed death. -/
def deathPrefixCount (B : Multiset (FiniteInterval s)) (b d : ℕ) : ℕ := by
  classical
  exact B.countP (fun I => I.birth ≤ b ∧ I.death = d)

private theorem count_death_step (B : Multiset (FiniteInterval s)) (b d : ℕ)
    (hd : 0 < d) :
    B.countP (fun I => I.birth ≤ b ∧ d - 1 < I.death) =
      deathPrefixCount B b d + B.countP (fun I => I.birth ≤ b ∧ d < I.death) := by
  classical
  induction B using Multiset.induction_on with
  | empty => simp [deathPrefixCount]
  | @cons I B ih =>
    simp only [deathPrefixCount, Multiset.countP_cons] at ih ⊢
    split_ifs <;> omega

private theorem count_terminal (B : Multiset (FiniteInterval s)) (b : ℕ) (hs : 0 < s) :
    B.countP (fun I => I.birth ≤ b ∧ s - 1 < I.death) = deathPrefixCount B b s := by
  classical
  unfold deathPrefixCount
  apply Multiset.countP_congr rfl
  intro I _
  have := I.death_le_size
  apply propext
  constructor
  · rintro ⟨hb, hd⟩
    exact ⟨hb, by omega⟩
  · rintro ⟨hb, hd⟩
    exact ⟨hb, by omega⟩

variable {k : Type u} [Field k]

/-- The actual image/kernel intersection at the stage immediately before a finite death.
The bounds supply both finite indices and justify the predecessor. -/
def deathSubspace (M : PModule.{u,0,u} k (Fin s)) (b d : ℕ) (hbd : b < d) (hd : d < s) :
    Submodule k (M.obj ⟨d - 1, by omega⟩) :=
  LinearMap.range (structureMapLinear M
    (show (⟨b, by omega⟩ : Fin s) ≤ ⟨d - 1, by omega⟩ from by
      change b ≤ d - 1; omega)) ⊓
    LinearMap.ker (structureMapLinear M
      (show (⟨d - 1, by omega⟩ : Fin s) ≤ ⟨d, hd⟩ from by
        change d - 1 ≤ d; omega))

private theorem finrank_restricted_kernel (M : PModule.{u,0,u} k (Fin s))
    {a c d : Fin s} (hac : a ≤ c) (hcd : c ≤ d) :
    Module.finrank k (LinearMap.ker ((structureMapLinear M hcd).comp
      (LinearMap.range (structureMapLinear M hac)).subtype)) =
    Module.finrank k (LinearMap.range (structureMapLinear M hac) ⊓
      LinearMap.ker (structureMapLinear M hcd) : Submodule k (M.obj c)) := by
  let U := LinearMap.range (structureMapLinear M hac)
  rw [← Submodule.finrank_map_subtype_eq U
    (LinearMap.ker ((structureMapLinear M hcd).comp U.subtype))]
  change Module.finrank k (Submodule.map U.subtype
    (LinearMap.ker ((structureMapLinear M hcd).domRestrict U))) = _
  rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]

/-- For `b < d < s`, the same-death prefix count is the dimension of the actual
image/kernel intersection. This statement does not form a terminal predecessor. -/
theorem deathPrefixCount_eq_finrank (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] (b d : ℕ) (hbd : b < d) (hd : d < s) :
    deathPrefixCount (rankBarcode M) b d =
      Module.finrank k (deathSubspace M b d hbd hd) := by
  let a : Fin s := ⟨b, by omega⟩
  let c : Fin s := ⟨d - 1, by omega⟩
  let e : Fin s := ⟨d, hd⟩
  have hac : a ≤ c := by change b ≤ d - 1; omega
  have hce : c ≤ e := by change d - 1 ≤ d; omega
  have hcounts := count_death_step (rankBarcode M) b d (by omega)
  have hbefore := structureMapRank_rankBarcode M a c hac
  have hafter := structureMapRank_rankBarcode M a e (hac.trans hce)
  rw [rank_barcodeMap] at hbefore hafter
  have hdrop := structureMapRank_drop M a c e hac hce
  rw [finrank_restricted_kernel] at hdrop
  change structureMapRank M a c hac = structureMapRank M a e (hac.trans hce) +
    Module.finrank k (deathSubspace M b d hbd hd) at hdrop
  change (rankBarcode M).countP (fun I => I.birth ≤ b ∧ d - 1 < I.death) = _ at hbefore
  change (rankBarcode M).countP (fun I => I.birth ≤ b ∧ d < I.death) = _ at hafter
  omega

/-- The terminal case counts the image at the last observed stage. The hypothesis
`b < s` implies `s > 0`; no index is formed when the chain is empty. -/
theorem deathPrefixCount_terminal (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] (b : ℕ) (hb : b < s) :
    deathPrefixCount (rankBarcode M) b s =
      structureMapRank M ⟨b, hb⟩ ⟨s - 1, by omega⟩ (by change b ≤ s - 1; omega) := by
  rw [← count_terminal _ _ (by omega)]
  have h := structureMapRank_rankBarcode M ⟨b, hb⟩ ⟨s - 1, by omega⟩
    (by change b ≤ s - 1; omega)
  rw [rank_barcodeMap] at h
  exact h

private theorem naturality_apply {M N : PModule.{u,0,u} k (Fin s)} (j : M ⟶ N)
    {a c : Fin s} (h : a ≤ c) (x : M.obj a) :
    (j.app c).hom (structureMapLinear M h x) =
      structureMapLinear N h ((j.app a).hom x) :=
  congrArg (fun f : M.obj a ⟶ N.obj c => f.hom x) (j.naturality (homOfLE h))

private def deathSubspaceMap {M N : PModule.{u,0,u} k (Fin s)} (j : M ⟶ N)
    (b d : ℕ) (hbd : b < d) (hd : d < s) :
    deathSubspace M b d hbd hd →ₗ[k] deathSubspace N b d hbd hd :=
  ((j.app ⟨d - 1, by omega⟩).hom.comp (deathSubspace M b d hbd hd).subtype).codRestrict
    (deathSubspace N b d hbd hd) (by
      intro x
      constructor
      · obtain ⟨y, hy⟩ := x.property.1
        refine ⟨(j.app ⟨b, by omega⟩).hom y, ?_⟩
        rw [← naturality_apply, hy]
        rfl
      · change structureMapLinear N _ ((j.app _).hom x.val) = 0
        rw [← naturality_apply, x.property.2, map_zero])

private theorem deathSubspaceMap_injective {M N : PModule.{u,0,u} k (Fin s)} (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) (b d : ℕ) (hbd : b < d) (hd : d < s) :
    Function.Injective (deathSubspaceMap j b d hbd hd) := by
  intro x y h
  apply Subtype.ext
  exact hj _ (congrArg Subtype.val h)

private def imageMap {M N : PModule.{u,0,u} k (Fin s)} (j : M ⟶ N)
    {a c : Fin s} (h : a ≤ c) :
    LinearMap.range (structureMapLinear M h) →ₗ[k] LinearMap.range (structureMapLinear N h) :=
  ((j.app c).hom.comp (LinearMap.range (structureMapLinear M h)).subtype).codRestrict _ (by
    rintro ⟨x, y, rfl⟩
    exact ⟨(j.app a).hom y, (naturality_apply j h y).symm⟩)

private theorem imageMap_injective {M N : PModule.{u,0,u} k (Fin s)} (j : M ⟶ N)
    (hj : ∀ i, Function.Injective (j.app i).hom) {a c : Fin s} (h : a ≤ c) :
    Function.Injective (imageMap j h) := by
  intro x y hxy
  apply Subtype.ext
  exact hj _ (congrArg Subtype.val hxy)

/-- A componentwise injection increases each cumulative count at one fixed death.
The proof compares actual restricted subspace injections, including terminal images. -/
theorem deathPrefixCount_le_of_injective {M N : PModule.{u,0,u} k (Fin s)}
    [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]
    (j : M ⟶ N) (hj : ∀ i, Function.Injective (j.app i).hom) (b d : ℕ)
    (hbd : b < d) (hd : d ≤ s) :
    deathPrefixCount (rankBarcode M) b d ≤ deathPrefixCount (rankBarcode N) b d := by
  by_cases hds : d < s
  · rw [deathPrefixCount_eq_finrank M b d hbd hds,
      deathPrefixCount_eq_finrank N b d hbd hds]
    exact LinearMap.finrank_le_finrank_of_injective (deathSubspaceMap_injective j hj b d hbd hds)
  · have hdeq : d = s := by omega
    subst d
    rw [deathPrefixCount_terminal M b hbd, deathPrefixCount_terminal N b hbd]
    exact LinearMap.finrank_le_finrank_of_injective (imageMap_injective j hj _)

end TDA.Persistence.FiniteBarcode
