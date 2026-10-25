/-
Copyright (c) 2025 Fabian Odermatt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Odermatt

The finite-partition proof in prism_sum_cancel is adapted from
Mathlib/AlgebraicTopology/SimplicialObject/ChainHomotopy.lean at
0df444a360eaa60ab8c11dca51a86af692955474. The adaptation separates the
additive cancellation from simplicial objects and supplies face tuple
identities and face membership for the signed prism constructed here.
-/
import TDA.Simplicial.Contiguity
import TDA.Simplicial.VertexChainMap
import Mathlib.Algebra.Homology.Homotopy

/-!
# Contiguity on signed simplicial chains

Two vertex maps are contiguous when the union of their images of each source
face is a target face. Their signed prism `P` satisfies `∂P + P∂ = g# - f#`
on the existing ordered-face complex, over every ring. In degree zero this
reduces to `∂P₀ = g₀ - f₀`. Mathlib's homotopy from `f#` to `g#` therefore
has component `-P`.

Contiguity supplies the face membership of every mixed tuple. Repeated
vertices are handled by the existing oriented-tuple cancellation theorem, so
the maps may identify vertices and the coefficient ring may have torsion.
-/

namespace TDA.Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Module
open scoped BigOperators

universe u v

noncomputable section

private def prismTuple {W : Type*} {n : ℕ} (a b : Fin (n + 1) → W)
    (i : Fin (n + 1)) (k : Fin (n + 2)) : W :=
  if h : k.val ≤ i.val then a ⟨k.val, by omega⟩ else b ⟨k.val - 1, by omega⟩

private theorem succAbove_val {n : ℕ} (j : Fin (n + 1)) (k : Fin n) :
    (j.succAbove k).val = if k.val < j.val then k.val else k.val + 1 := by
  by_cases h : k.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have hv : k.val < j.val := h
    simp only [Fin.val_castSucc, if_pos hv]
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
    have hv : ¬k.val < j.val := h
    simp only [Fin.val_succ, if_neg hv]

private theorem prism_delete_before {W : Type*} {n : ℕ}
    (a b : Fin (n + 2) → W) (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : i.castSucc < j) :
    prismTuple (a ∘ j.succAbove) (b ∘ j.succAbove) i =
      prismTuple a b i.castSucc ∘ j.succ.succAbove := by
  funext k
  have hv := succAbove_val j.succ k
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h hv
  simp only [prismTuple, Function.comp_apply, Fin.val_castSucc]
  split_ifs <;> split_ifs at hv <;> try omega
  all_goals
    congr 1
    apply Fin.ext
    simp only [succAbove_val, Fin.val_succ]; split_ifs <;> omega

private theorem prism_delete_after {W : Type*} {n : ℕ}
    (a b : Fin (n + 2) → W) (i : Fin (n + 1)) (j : Fin (n + 2))
    (h : ¬i.castSucc < j) :
    prismTuple (a ∘ j.succAbove) (b ∘ j.succAbove) i =
      prismTuple a b i.succ ∘ j.castSucc.succAbove := by
  funext k
  have hv := succAbove_val j.castSucc k
  simp only [Fin.lt_def, Fin.val_castSucc] at h hv
  simp only [prismTuple, Function.comp_apply, Fin.val_succ]
  split_ifs <;> split_ifs at hv <;> try omega
  all_goals
    congr 1
    apply Fin.ext
    simp only [succAbove_val, Fin.val_castSucc] <;> split_ifs <;> omega

private theorem prism_delete_interface {W : Type*} {n : ℕ}
    (a b : Fin (n + 2) → W) (i : Fin (n + 1)) :
    prismTuple a b i.succ ∘ i.castSucc.succ.succAbove =
      prismTuple a b i.castSucc ∘ i.castSucc.succ.succAbove := by
  funext k
  have hv := succAbove_val i.castSucc.succ k
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  simp only [prismTuple, Function.comp_apply, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> split_ifs at hv <;> first | omega | rfl

private theorem prism_delete_first {W : Type*} {n : ℕ} (a b : Fin (n + 1) → W) :
    prismTuple a b 0 ∘ (0 : Fin (n + 2)).succAbove = b := by
  funext k
  simp [prismTuple, Fin.succAbove_zero]

private theorem prism_delete_last {W : Type*} {n : ℕ} (a b : Fin (n + 1) → W) :
    prismTuple a b (Fin.last n) ∘ (Fin.last (n + 1)).succAbove = a := by
  funext k
  simp [prismTuple, Fin.succAbove_last, Nat.le_of_lt_succ k.isLt]

-- The source-boundary terms α cancel the prism-boundary terms β away from
-- the two interface faces. Adjacent interface terms cancel each other, leaving
-- the two endpoint faces. The finite partition adapts mathlib's
-- SimplicialObject/ChainHomotopy (Fabian Odermatt, Apache-2.0).
private theorem prism_sum_cancel {A : Type*} [AddCommGroup A] (n : ℕ)
    (α : Fin (n + 1) × Fin (n + 2) → A)
    (β : Fin (n + 3) × Fin (n + 2) → A)
    (hb : ∀ x, x.1.castSucc < x.2 → α x = -β (x.2.succ, x.1.castSucc))
    (ha : ∀ x, ¬x.1.castSucc < x.2 → α x = -β (x.2.castSucc, x.1.succ))
    (hi : ∀ i : Fin (n + 1), β (i.castSucc.succ, i.castSucc) =
      -β (i.castSucc.succ, i.succ)) :
    (∑ x, α x) + (∑ y, β y) = β (0, 0) + β (Fin.last _, Fin.last _) := by
  classical
  let S : Finset (Fin (n + 1) × Fin (n + 2)) := { x | x.1.castSucc < x.2 }
  let γ₁ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.castSucc, x.1.succ)
  let γ₂ (x : Fin (n + 1) × Fin (n + 2)) := (x.2.succ, x.1.castSucc)
  let γ₃ (i : Fin (n + 1)) := (i.castSucc.succ, i.succ)
  let γ₄ (i : Fin (n + 1)) := (i.castSucc.succ, i.castSucc)
  have hγ₁ : Function.Injective γ₁ := fun _ _ ↦ by aesop
  have hγ₂ : Function.Injective γ₂ := fun _ _ ↦ by aesop
  have hγ₃ : Function.Injective γ₃ := fun _ _ ↦ by aesop
  have hγ₄ : Function.Injective γ₄ := fun _ _ ↦ by aesop
  have eq₃ : ∑ x ∈ Sᶜ, α x = - ∑ y ∈ Finset.image γ₁ Sᶜ, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₁.injOn]
    apply Finset.sum_congr rfl
    intro x hx
    exact ha x (by simpa [S] using hx)
  have eq₄ : ∑ x ∈ S, α x = - ∑ y ∈ Finset.image γ₂ S, β y := by
    rw [← Finset.sum_neg_distrib, Finset.sum_image hγ₂.injOn]
    apply Finset.sum_congr rfl
    intro x hx
    exact hb x (by simpa [S] using hx)
  have eq₅ : ∑ x, β (γ₄ x) = - ∑ x, β (γ₃ x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  have h₁ : Disjoint (Finset.image γ₁ Sᶜ) (Finset.image γ₂ S) := by
    rw [Finset.disjoint_iff_ne]
    grind [Finset.mem_compl]
  have h₂ : Disjoint (Finset.image γ₃ .univ) (Finset.image γ₄ .univ) := by
    rw [Finset.disjoint_iff_ne]
    grind
  have h₃ : Disjoint (Finset.disjUnion _ _ h₂) {(0, 0), (Fin.last _, Fin.last _)} := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.mem_insert, forall_eq_or_imp, Prod.forall]
    rintro ⟨a, _⟩ ⟨b, _⟩
    simp
    grind
  have h₄ : Disjoint (Finset.disjUnion _ _ h₁) (Finset.disjUnion _ _ h₃) := by
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.compl_filter, not_lt, Finset.disjUnion_eq_union, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists, ne_eq,
      Finset.mem_insert, Finset.mem_singleton, Prod.forall, Prod.mk.injEq, not_and,
      S, γ₁, γ₂, γ₃, γ₄]
    rintro ⟨a, _⟩ ⟨b, _⟩ (⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩ | ⟨⟨j, _⟩, ⟨k, _⟩, h₁, h₂, h₃⟩) _ _
      ((⟨⟨i, _⟩, h₄, h₅⟩ | ⟨⟨i, _⟩, h₄, h₅⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)) <;>
        simp [Fin.ext_iff] at h₁ h₂ h₃ ⊢ <;> grind
  have H : (Finset.disjUnion _ _ h₁)ᶜ = Finset.disjUnion _ _ h₃ :=
    Finset.compl_eq_of_disjoint_of_card_add_eq h₄ (by
      rw [Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_disjUnion,
        Finset.card_image_of_injective _ hγ₁, Finset.card_image_of_injective _ hγ₂,
        Finset.card_image_of_injective _ hγ₃, Finset.card_image_of_injective _ hγ₄]
      simp
      lia)
  rw [← S.sum_add_sum_compl, eq₃, eq₄]
  rw [← neg_add_rev, ← Finset.sum_disjUnion h₁, ← (Finset.disjUnion _ _ h₁).sum_add_sum_compl,
    H]
  simp only [Finset.sum_disjUnion]
  rw [Finset.sum_image hγ₃.injOn, Finset.sum_image hγ₄.injOn,
    Finset.sum_insert (by simp), Finset.sum_singleton, eq₅]
  abel

variable {W : Type u} [LinearOrder W]

private def tuplePrism (L : PreAbstractSimplicialComplex W) (R : Type v) [Ring R]
    {n : ℕ} (a b : Fin (n + 1) → W) : Chain L R (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • orientedTuple L R (prismTuple a b i)

private theorem prismTuple_mem (L : PreAbstractSimplicialComplex W) {n : ℕ}
    (a b : Fin (n + 1) → W)
    (hk : Finset.univ.image a ∪ Finset.univ.image b ∈ L) (i : Fin (n + 1)) :
    Finset.univ.image (prismTuple a b i) ∈ L := by
  classical
  apply (L.isRelLowerSet_faces hk).2
  · intro w hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    unfold prismTuple
    split_ifs
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
  · exact Finset.image_nonempty.mpr Finset.univ_nonempty

private theorem tuplePrism_boundary (L : PreAbstractSimplicialComplex W)
    (R : Type v) [Ring R] {n : ℕ} (a b : Fin (n + 2) → W)
    (hprism : ∀ i : Fin (n + 2),
      Finset.univ.image (prismTuple a b i) ∈ L) :
    boundary L R (n + 1) (tuplePrism L R a b) +
        (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          tuplePrism L R (a ∘ j.succAbove) (b ∘ j.succAbove)) =
      orientedTuple L R b - orientedTuple L R a := by
  let α (x : Fin (n + 1) × Fin (n + 2)) : Chain L R (n + 1) :=
    (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ)) •
      orientedTuple L R (prismTuple (a ∘ x.2.succAbove) (b ∘ x.2.succAbove) x.1)
  let β (x : Fin (n + 3) × Fin (n + 2)) : Chain L R (n + 1) :=
    (-1 : ℤ) ^ ((x.1 : ℕ) + (x.2 : ℕ)) •
      orientedTuple L R (prismTuple a b x.2 ∘ x.1.succAbove)
  have hb : ∀ x, x.1.castSucc < x.2 → α x = -β (x.2.succ, x.1.castSucc) := by
    rintro ⟨i, j⟩ hij
    dsimp only [α, β, Fin.val_succ, Fin.val_castSucc]
    rw [prism_delete_before a b i j hij,
      show (j.val + 1 + i.val) = (i.val + j.val) + 1 by omega]
    simp [pow_succ]
  have ha : ∀ x, ¬x.1.castSucc < x.2 → α x = -β (x.2.castSucc, x.1.succ) := by
    rintro ⟨i, j⟩ hij
    dsimp only [α, β, Fin.val_succ, Fin.val_castSucc]
    rw [prism_delete_after a b i j hij,
      show j.val + (i.val + 1) = (i.val + j.val) + 1 by omega]
    simp [pow_succ]
  have hi : ∀ i : Fin (n + 1), β (i.castSucc.succ, i.castSucc) =
      -β (i.castSucc.succ, i.succ) := by
    intro i
    dsimp only [β, Fin.val_succ, Fin.val_castSucc]
    rw [prism_delete_interface,
      show (i.val + 1) + (i.val + 1) = ((i.val + 1) + i.val) + 1 by omega]
    simp [pow_succ]
  have hα : (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
      tuplePrism L R (a ∘ j.succAbove) (b ∘ j.succAbove)) = ∑ x, α x := by
    unfold tuplePrism
    simp only [Finset.smul_sum, smul_smul, ← pow_add]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    simp only [α, Nat.add_comm]
  have hβ : boundary L R (n + 1) (tuplePrism L R a b) = ∑ x, β x := by
    unfold tuplePrism
    rw [map_sum]
    simp only [map_zsmul]
    simp_rw [boundary_orientedTuple L R _ (hprism _)]
    simp only [tupleBoundarySum, Finset.smul_sum, smul_smul, ← pow_add]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    simp only [β, Nat.add_comm]
  have he : β (0, 0) = orientedTuple L R b := by
    dsimp only [β, Fin.val_zero]
    rw [prism_delete_first]
    simp
  have hl : β (Fin.last _, Fin.last _) = -orientedTuple L R a := by
    dsimp only [β, Fin.val_last]
    rw [prism_delete_last,
      show n + 2 + (n + 1) = 2 * (n + 1) + 1 by omega, pow_add, pow_mul]
    norm_num
  rw [hα, hβ, add_comm (∑ x, β x) (∑ x, α x)]
  exact (prism_sum_cancel n α β hb ha hi).trans (by rw [he, hl, sub_eq_add_neg])

private theorem tuplePrism_boundary_zero (L : PreAbstractSimplicialComplex W)
    (R : Type v) [Ring R] (a b : Fin 1 → W)
    (hprism : ∀ i : Fin 1, Finset.univ.image (prismTuple a b i) ∈ L) :
    boundary L R 0 (tuplePrism L R a b) = orientedTuple L R b - orientedTuple L R a := by
  change boundary L R 0 (∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) •
    orientedTuple L R (prismTuple a b i)) = _
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [boundary_orientedTuple L R _ (hprism 0)]
  unfold tupleBoundarySum
  rw [Fin.sum_univ_two]
  have hf := prism_delete_first a b
  have hl := prism_delete_last a b
  change prismTuple a b 0 ∘ (1 : Fin 2).succAbove = a at hl
  rw [hf, hl]
  simp [sub_eq_add_neg]

variable {V : Type u} [LinearOrder V]
variable {K : PreAbstractSimplicialComplex V} {L : PreAbstractSimplicialComplex W}
variable (R : Type v) [Ring R]
variable {f g : VertexMap K L}

/-- Every mixed prism tuple over each source face is a target face.  This
weaker, cut-by-cut condition suffices for the signed prism homotopy; it does
not require the union of the two endpoint images to be a face. -/
def PrismAdmissible (f g : VertexMap K L) : Prop :=
  ∀ {n : ℕ} (s : Face K n) (i : Fin (n + 1)),
    Finset.univ.image
      (prismTuple (f ∘ s.1.orderEmbOfFin s.2.2)
        (g ∘ s.1.orderEmbOfFin s.2.2) i) ∈ L

namespace PrismAdmissible

private def prismMap (h : PrismAdmissible f g) (n : ℕ) :
    Chain K R n →ₗ[R] Chain L R (n + 1) :=
  Finsupp.linearCombination R (fun s : Face K n =>
    tuplePrism L R (f ∘ s.1.orderEmbOfFin s.2.2) (g ∘ s.1.orderEmbOfFin s.2.2))

private theorem prismMap_single_tuple (h : PrismAdmissible f g) (n : ℕ)
    (s : Face K n) (a : R) :
    prismMap R h n (Finsupp.single s a) =
      a • tuplePrism L R (f ∘ s.1.orderEmbOfFin s.2.2)
        (g ∘ s.1.orderEmbOfFin s.2.2) := by
  simp [prismMap]

private theorem boundary_prismMap_zero (h : PrismAdmissible f g) :
    (boundary L R 0).comp (prismMap R h 0) =
      vertexChainMap R g 0 - vertexChainMap R f 0 := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change boundary L R 0 (prismMap R h 0 (Finsupp.single s 1)) =
    vertexChainMap R g 0 (Finsupp.single s 1) -
      vertexChainMap R f 0 (Finsupp.single s 1)
  simp only [prismMap_single_tuple, vertexChainMap_single, one_smul]
  exact tuplePrism_boundary_zero L R _ _ (fun i => h s i)

private theorem boundary_prismMap_succ (h : PrismAdmissible f g) (n : ℕ) :
    (boundary L R (n + 1)).comp (prismMap R h (n + 1)) +
      (prismMap R h n).comp (boundary K R n) =
        vertexChainMap R g (n + 1) - vertexChainMap R f (n + 1) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change boundary L R (n + 1) (prismMap R h (n + 1) (Finsupp.single s 1)) +
      prismMap R h n (boundary K R n (Finsupp.single s 1)) =
    vertexChainMap R g (n + 1) (Finsupp.single s 1) -
      vertexChainMap R f (n + 1) (Finsupp.single s 1)
  simp only [prismMap_single_tuple, vertexChainMap_single, one_smul]
  have hd : prismMap R h n (boundary K R n (Finsupp.single s 1)) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • tuplePrism L R
        ((f ∘ s.1.orderEmbOfFin s.2.2) ∘ j.succAbove)
        ((g ∘ s.1.orderEmbOfFin s.2.2) ∘ j.succAbove) := by
    rw [boundary_single, one_smul, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [prismMap_single_tuple]
    have he : ⇑((deletedFace K n s j).1.orderEmbOfFin (deletedFace K n s j).2.2) =
        s.1.orderEmbOfFin s.2.2 ∘ j.succAbove := by
      funext k
      exact enumerationAfterDeletion K n s j _ k
    rw [he]
    have hs : (-1 : R) ^ (j : ℕ) = (((-1 : ℤ) ^ (j : ℕ) : ℤ) : R) := by norm_cast
    rw [hs, Int.cast_smul_eq_zsmul]
    rfl
  rw [hd]
  exact tuplePrism_boundary L R _ _ (fun i => h s i)

private def homotopyComponent (h : PrismAdmissible f g) (i j : ℕ) :
    (simplicialChainComplex K R).X i ⟶ (simplicialChainComplex L R).X j :=
  if hij : i + 1 = j then
    ModuleCat.ofHom (-prismMap R h i) ≫
      eqToHom (congrArg (fun k => (simplicialChainComplex L R).X k) hij)
  else 0

private theorem homotopyComponent_succ (h : PrismAdmissible f g) (i : ℕ) :
    homotopyComponent R h i (i + 1) = ModuleCat.ofHom (-prismMap R h i) := by
  simp [homotopyComponent]

/-- The chain homotopy constructed from the mixed prism tuples. -/
def chainHomotopy (h : PrismAdmissible f g) :
    Homotopy (simplicialChainMap R f) (simplicialChainMap R g) where
  hom := homotopyComponent R h
  zero i j hij := dif_neg hij
  comm i := by
    cases i with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp), dNext_eq_zero _ _ (by simp), zero_add]
      simp only [homotopyComponent_succ, simplicialChainMap_f, simplicialChainComplex_d]
      apply ModuleCat.hom_ext
      change vertexChainMap R f 0 =
        (boundary L R 0).comp (-prismMap R h 0) + vertexChainMap R g 0
      rw [LinearMap.comp_neg, boundary_prismMap_zero]
      abel
    | succ n =>
      rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 2) (w := by simp)]
      simp only [homotopyComponent_succ, simplicialChainMap_f, simplicialChainComplex_d]
      apply ModuleCat.hom_ext
      change vertexChainMap R f (n + 1) =
        (-prismMap R h n).comp (boundary K R n) +
          (boundary L R (n + 1)).comp (-prismMap R h (n + 1)) +
          vertexChainMap R g (n + 1)
      rw [LinearMap.neg_comp, LinearMap.comp_neg]
      calc
        _ = -(vertexChainMap R g (n + 1) - vertexChainMap R f (n + 1)) +
            vertexChainMap R g (n + 1) := by abel
        _ = -((boundary L R (n + 1)).comp (prismMap R h (n + 1)) +
            (prismMap R h n).comp (boundary K R n)) +
            vertexChainMap R g (n + 1) := by rw [boundary_prismMap_succ]
        _ = _ := by abel

end PrismAdmissible

/-- Vertex maps with every mixed prism tuple a target face induce equal maps
on simplicial homology. -/
theorem simplicialHomologyMap_eq_of_prismAdmissible (h : PrismAdmissible f g) (n : ℕ) :
    TDA.Simplicial.simplicialHomologyMap R f n =
      TDA.Simplicial.simplicialHomologyMap R g n :=
  (PrismAdmissible.chainHomotopy R h).homologyMap_eq n

namespace Contiguous

/-- The positive signed prism of two contiguous maps on ordered faces. -/
def prismMap (_h : Contiguous f g) (n : ℕ) : Chain K R n →ₗ[R] Chain L R (n + 1) :=
  Finsupp.linearCombination R (fun s : Face K n =>
    tuplePrism L R (f ∘ s.1.orderEmbOfFin s.2.2) (g ∘ s.1.orderEmbOfFin s.2.2))

private theorem prismMap_single_tuple (h : Contiguous f g) (n : ℕ) (s : Face K n) (a : R) :
    prismMap R h n (Finsupp.single s a) =
      a • tuplePrism L R (f ∘ s.1.orderEmbOfFin s.2.2) (g ∘ s.1.orderEmbOfFin s.2.2) := by
  simp [prismMap]

/-- On a basis face the prism is the alternating mixed-tuple sum, with the left coefficient. -/
theorem prismMap_single (h : Contiguous f g) (n : ℕ) (s : Face K n) (a : R) :
    prismMap R h n (Finsupp.single s a) = a •
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • orientedTuple L R
        (fun k : Fin (n + 2) => if hi : k.val ≤ i.val then
          f (s.1.orderEmbOfFin s.2.2 ⟨k.val, by omega⟩) else
          g (s.1.orderEmbOfFin s.2.2 ⟨k.val - 1, by omega⟩)) := by
  rw [prismMap_single_tuple]
  rfl

private theorem face_union_mem (h : Contiguous f g) {n : ℕ} (s : Face K n) :
    Finset.univ.image (f ∘ s.1.orderEmbOfFin s.2.2) ∪
      Finset.univ.image (g ∘ s.1.orderEmbOfFin s.2.2) ∈ L := by
  classical
  have he (q : V → W) : Finset.univ.image (q ∘ s.1.orderEmbOfFin s.2.2) =
      @Finset.image V W (Classical.decEq W) q s.1 := by
    rw [← Finset.image_image, Finset.image_orderEmbOfFin_univ]
    ext w
    simp only [Finset.mem_image]
  rw [he f, he g]
  convert h s.1 s.2.1 using 1
  ext w
  simp only [Finset.mem_union]

private theorem prismAdmissible_of_contiguous (h : Contiguous f g) :
    PrismAdmissible f g := by
  intro n s i
  exact prismTuple_mem L _ _ (face_union_mem h s) i

/-- In degree zero the prism has boundary equal to the difference of the endpoint maps. -/
theorem boundary_prismMap_zero (h : Contiguous f g) :
    (boundary L R 0).comp (prismMap R h 0) = vertexChainMap R g 0 - vertexChainMap R f 0 := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change boundary L R 0 (prismMap R h 0 (Finsupp.single s 1)) =
    vertexChainMap R g 0 (Finsupp.single s 1) - vertexChainMap R f 0 (Finsupp.single s 1)
  simp only [prismMap_single_tuple, vertexChainMap_single, one_smul]
  exact tuplePrism_boundary_zero L R _ _ (fun i => prismAdmissible_of_contiguous h s i)

/-- In every positive degree the prism satisfies the signed chain-homotopy equation. -/
theorem boundary_prismMap_succ (h : Contiguous f g) (n : ℕ) :
    (boundary L R (n + 1)).comp (prismMap R h (n + 1)) +
      (prismMap R h n).comp (boundary K R n) =
        vertexChainMap R g (n + 1) - vertexChainMap R f (n + 1) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change boundary L R (n + 1) (prismMap R h (n + 1) (Finsupp.single s 1)) +
      prismMap R h n (boundary K R n (Finsupp.single s 1)) =
    vertexChainMap R g (n + 1) (Finsupp.single s 1) -
      vertexChainMap R f (n + 1) (Finsupp.single s 1)
  simp only [prismMap_single_tuple, vertexChainMap_single, one_smul]
  have hd : prismMap R h n (boundary K R n (Finsupp.single s 1)) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • tuplePrism L R
        ((f ∘ s.1.orderEmbOfFin s.2.2) ∘ j.succAbove)
        ((g ∘ s.1.orderEmbOfFin s.2.2) ∘ j.succAbove) := by
    rw [boundary_single, one_smul, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [prismMap_single_tuple]
    have he : ⇑((deletedFace K n s j).1.orderEmbOfFin (deletedFace K n s j).2.2) =
        s.1.orderEmbOfFin s.2.2 ∘ j.succAbove := by
      funext k
      exact enumerationAfterDeletion K n s j _ k
    rw [he]
    have hs : (-1 : R) ^ (j : ℕ) = (((-1 : ℤ) ^ (j : ℕ) : ℤ) : R) := by norm_cast
    rw [hs, Int.cast_smul_eq_zsmul]
    rfl
  rw [hd]
  exact tuplePrism_boundary L R _ _ (fun i => prismAdmissible_of_contiguous h s i)

private def homotopyComponent (h : Contiguous f g) (i j : ℕ) :
    (simplicialChainComplex K R).X i ⟶ (simplicialChainComplex L R).X j :=
  if hij : i + 1 = j then
    ModuleCat.ofHom (-prismMap R h i) ≫
      eqToHom (congrArg (fun k => (simplicialChainComplex L R).X k) hij)
  else 0

private theorem homotopyComponent_succ (h : Contiguous f g) (i : ℕ) :
    homotopyComponent R h i (i + 1) = ModuleCat.ofHom (-prismMap R h i) := by
  simp [homotopyComponent]

/-- The chain homotopy of contiguous maps. Its component is the negative prism. -/
def chainHomotopy (h : Contiguous f g) :
    Homotopy (simplicialChainMap R f) (simplicialChainMap R g) where
  hom := homotopyComponent R h
  zero i j hij := by
    exact dif_neg hij
  comm i := by
    cases i with
    | zero =>
      rw [prevD_eq (j' := 1) (w := by simp), dNext_eq_zero _ _ (by simp), zero_add]
      simp only [homotopyComponent_succ, simplicialChainMap_f, simplicialChainComplex_d]
      apply ModuleCat.hom_ext
      change vertexChainMap R f 0 =
        (boundary L R 0).comp (-prismMap R h 0) + vertexChainMap R g 0
      rw [LinearMap.comp_neg, boundary_prismMap_zero]
      abel
    | succ n =>
      rw [dNext_eq (i' := n) (w := by simp), prevD_eq (j' := n + 2) (w := by simp)]
      simp only [homotopyComponent_succ, simplicialChainMap_f, simplicialChainComplex_d]
      apply ModuleCat.hom_ext
      change vertexChainMap R f (n + 1) =
        (-prismMap R h n).comp (boundary K R n) +
          (boundary L R (n + 1)).comp (-prismMap R h (n + 1)) + vertexChainMap R g (n + 1)
      rw [LinearMap.neg_comp, LinearMap.comp_neg]
      calc
        _ = -(vertexChainMap R g (n + 1) - vertexChainMap R f (n + 1)) +
            vertexChainMap R g (n + 1) := by abel
        _ = -((boundary L R (n + 1)).comp (prismMap R h (n + 1)) +
            (prismMap R h n).comp (boundary K R n)) + vertexChainMap R g (n + 1) := by
          rw [boundary_prismMap_succ]
        _ = _ := by abel

/-- The degree-raising component of the constructed homotopy is exactly minus the prism. -/
@[simp] theorem chainHomotopy_hom_succ (h : Contiguous f g) (n : ℕ) :
    (chainHomotopy R h).hom n (n + 1) = ModuleCat.ofHom (-prismMap R h n) :=
  homotopyComponent_succ R h n

/-- The constructed homotopy vanishes off its degree-raising shape. -/
theorem chainHomotopy_hom_eq_zero (h : Contiguous f g) (i j : ℕ) (hij : i + 1 ≠ j) :
    (chainHomotopy R h).hom i j = 0 := by
  exact dif_neg hij

/-- Contiguous arbitrary vertex maps induce equal maps on the existing homology. -/
theorem simplicialHomologyMap_eq (h : Contiguous f g) (n : ℕ) :
    TDA.Simplicial.simplicialHomologyMap R f n = TDA.Simplicial.simplicialHomologyMap R g n :=
  simplicialHomologyMap_eq_of_prismAdmissible R (prismAdmissible_of_contiguous h) n

end Contiguous

end
end TDA.Simplicial
