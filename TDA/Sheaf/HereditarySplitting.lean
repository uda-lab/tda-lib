import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Data.Int.Interval

/-!
# Hereditary splitting in the bounded derived category

Let `C` be an abelian category with a derived category `D(C)` (`[HasDerivedCategory C]`), and
write `Hⁱ = DerivedCategory.homologyFunctor C i` and `X[-i] = (singleFunctor C i).obj X` for the
object `X` placed in degree `i`. Degrees are those of the canonical t-structure of Mathlib:
`K.IsGE a` and `K.IsLE b` say that `Hⁱ K = 0` outside `[a, b]`.

* `exists_iso_biproduct_homology`: a bounded `K` (`K.IsGE a`, `K.IsLE b`) such that
  `Ext^{j - i + 1}(Hʲ K, Hⁱ K) = 0` for all `a ≤ i < j ≤ b` is isomorphic to the finite direct
  sum `⨁_{i ∈ [a, b]} (Hⁱ K)[-i]`, indexed by `Finset.Icc a b`. The isomorphism is not canonical:
  the statement is `Nonempty`. `exists_iso_biproduct_homology_of_two_le` is the case of the
  blanket hypothesis `Ext^n(Hʲ K, Hⁱ K) = 0` for all `i`, `j` and `n ≥ 2` (hereditary `C`).

  The proof inducts on the length of `[a, b]` with Mathlib's truncation triangle
  `τ_{< b} K ⟶ K ⟶ τ_{≥ b} K ⟶ (τ_{< b} K)[1]` (`TStructure.triangleLTGE`). By induction
  `τ_{< b} K ≅ ⨁_{i < b} (Hⁱ K)[-i]`, and `τ_{≥ b} K ≅ (Hᵇ K)[-b]`; the connecting morphism has
  components `(Hᵇ K)[-b] ⟶ (Hⁱ K)[-i][1]`, which are classes in `Ext^{b - i + 1}(Hᵇ K, Hⁱ K) = 0`
  (`singleFunctor_hom_eq_zero_of_ext`). A distinguished triangle with zero connecting morphism
  splits (Mathlib's `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`).
* The truncations compute cohomology: `isIso_homologyMap_truncLTι` (`Hⁱ (τ_{< n} K) ≅ Hⁱ K` for
  `i < n`) and `isIso_homologyMap_truncGEπ` (`Hⁱ K ≅ Hⁱ (τ_{≥ n} K)` for `n ≤ i`), and an object
  concentrated in degree `n` is `(Hⁿ K)[-n]` (`nonempty_iso_singleFunctor_homology`).
* Cohomology of a sum of shifted objects. For a finite set `S` of degrees and objects `X i`,
  `homologyBiproductSingleIso`: `Hⁱ (⨁_{x ∈ S} (X x)[-x]) ≅ X i` for `i ∈ S`, and
  `isZero_homology_biproduct_single`: it is zero for `i ∉ S`. Hence a decomposition determines its
  summands: `nonempty_iso_homology_of_iso_biproduct_single` (`K ≅ ⨁_{x ∈ S} (X x)[-x]` gives
  `X i ≅ Hⁱ K`) and `nonempty_iso_of_iso_biproduct_single` (two isomorphic such sums have
  isomorphic summands degree by degree).
* Finite biproducts: `biproductInsertIso` (`(⨁_{i ∈ S} f i) ⊞ f j ≅ ⨁_{i ∈ insert j S} f i` for
  `j ∉ S`), `biproductIsoOfIsZero` (a biproduct whose summands other than `f j` are zero is
  `f j`) and `isZero_biproduct_of_isZero`.
-/

open CategoryTheory Limits Pretriangulated Triangulated DerivedCategory Abelian

namespace TDA.Sheaf

/-! ### Finite biproducts -/

section Biproduct

variable {D : Type*} [Category* D] [Preadditive D]

/-- **Inserting an index into a finite biproduct.** For `j ∉ S`,
`(⨁_{i ∈ S} f i) ⊞ f j ≅ ⨁_{i ∈ insert j S} f i`, with the summand inclusions of `S` and of `j`
matching those of `insert j S` (`inl_biproductInsertIso_hom`, `inr_biproductInsertIso_hom`). -/
noncomputable def biproductInsertIso [HasFiniteBiproducts D] [HasBinaryBiproducts D] {α : Type*}
    [DecidableEq α] (f : α → D) {S : Finset α} {j : α} (hj : j ∉ S) :
    (⨁ fun i : S => f i) ⊞ f j ≅ ⨁ fun i : ↥(insert j S) => f i := by
  let g : ↥(insert j S) → D := fun i => f i
  let incl : S → ↥(insert j S) := fun i => ⟨i, Finset.mem_insert_of_mem i.2⟩
  let jT : ↥(insert j S) := ⟨j, Finset.mem_insert_self j S⟩
  have hincl : ∀ i, incl i ≠ jT := fun i h => hj (by
    have h' : (i : α) = j := congrArg Subtype.val h
    rw [← h']
    exact i.2)
  have hinj : Function.Injective incl := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  let b : BinaryBicone (⨁ fun i : S => f i) (f j) :=
    { pt := ⨁ g
      fst := biproduct.lift fun i => biproduct.π g (incl i)
      snd := biproduct.π g jT
      inl := biproduct.desc fun i => biproduct.ι g (incl i)
      inr := biproduct.ι g jT
      inl_fst := by
        refine biproduct.hom_ext' _ _ fun x => biproduct.hom_ext _ _ fun y => ?_
        simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id]
        by_cases h : x = y
        · subst h; simp; rfl
        · rw [biproduct.ι_π_ne _ (hinj.ne h), biproduct.ι_π_ne _ h]
      inl_snd := by
        refine biproduct.hom_ext' _ _ fun x => ?_
        simp only [biproduct.ι_desc_assoc, comp_zero]
        exact biproduct.ι_π_ne _ (hincl x)
      inr_fst := by
        refine biproduct.hom_ext _ _ fun y => ?_
        simp only [Category.assoc, biproduct.lift_π, zero_comp]
        exact biproduct.ι_π_ne _ (hincl y).symm
      inr_snd := biproduct.ι_π_self _ _ }
  refine (biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal b ?_)).symm
  refine biproduct.hom_ext' _ _ fun x => ?_
  obtain ⟨x, hx⟩ := x
  rcases Finset.mem_insert.1 hx with rfl | hxS
  · have h₁ : biproduct.ι g ⟨x, hx⟩ ≫ b.fst = 0 := by
      refine biproduct.hom_ext _ _ fun y => ?_
      simp only [b, Category.assoc, biproduct.lift_π, zero_comp]
      exact biproduct.ι_π_ne _ (hincl y).symm
    simp only [Preadditive.comp_add, reassoc_of% h₁, zero_comp, zero_add]
    simp [b, jT]
  · have h₁ : biproduct.ι g ⟨x, hx⟩ ≫ b.fst = biproduct.ι (fun i : S => f i) ⟨x, hxS⟩ := by
      refine biproduct.hom_ext _ _ fun y => ?_
      simp only [b, Category.assoc, biproduct.lift_π]
      by_cases h : (⟨x, hxS⟩ : S) = y
      · subst h; simp [incl]; rfl
      · rw [biproduct.ι_π_ne _ h, biproduct.ι_π_ne]
        exact fun h' => h (hinj h')
    have h₂ : biproduct.ι g ⟨x, hx⟩ ≫ b.snd = 0 :=
      biproduct.ι_π_ne _ (hincl ⟨x, hxS⟩)
    simp only [Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂, zero_comp, add_zero]
    simp [b, incl]

/-- The summands of `S` enter `⨁_{i ∈ insert j S} f i` through `biproductInsertIso` by their own
inclusions. -/
theorem inl_biproductInsertIso_hom [HasFiniteBiproducts D] [HasBinaryBiproducts D] {α : Type*}
    [DecidableEq α] (f : α → D) {S : Finset α} {j : α} (hj : j ∉ S) (i : S) :
    biproduct.ι (fun i : S => f i) i ≫ biprod.inl ≫ (biproductInsertIso f hj).hom =
      biproduct.ι (fun i : ↥(insert j S) => f i) ⟨i, Finset.mem_insert_of_mem i.2⟩ := by
  simp [biproductInsertIso, biprod.uniqueUpToIso]

/-- The summand `f j` enters `⨁_{i ∈ insert j S} f i` through `biproductInsertIso` by its own
inclusion. -/
theorem inr_biproductInsertIso_hom [HasFiniteBiproducts D] [HasBinaryBiproducts D] {α : Type*}
    [DecidableEq α] (f : α → D) {S : Finset α} {j : α} (hj : j ∉ S) :
    biprod.inr ≫ (biproductInsertIso f hj).hom =
      biproduct.ι (fun i : ↥(insert j S) => f i) ⟨j, Finset.mem_insert_self j S⟩ := by
  simp [biproductInsertIso, biprod.uniqueUpToIso]

/-- **A biproduct with a single nonzero summand.** If every summand other than `f j` is zero,
the projection `⨁ f ⟶ f j` is an isomorphism, with inverse the inclusion. -/
@[simps]
noncomputable def biproductIsoOfIsZero {J : Type*} [Fintype J] [DecidableEq J] (f : J → D)
    [HasBiproduct f] (j : J) (h : ∀ x, x ≠ j → IsZero (f x)) : ⨁ f ≅ f j where
  hom := biproduct.π f j
  inv := biproduct.ι f j
  hom_inv_id := by
    rw [← biproduct.total, Finset.sum_eq_single j]
    · intro x _ hx
      rw [(h x hx).eq_of_tgt (biproduct.π f x) 0, zero_comp]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  inv_hom_id := biproduct.ι_π_self f j

/-- A finite biproduct of zero objects is zero. -/
theorem isZero_biproduct_of_isZero {J : Type*} [Fintype J] (f : J → D) [HasBiproduct f]
    (h : ∀ x, IsZero (f x)) :
    IsZero (⨁ f) := by
  rw [IsZero.iff_id_eq_zero, ← biproduct.total]
  exact Finset.sum_eq_zero fun x _ => by rw [(h x).eq_of_tgt (biproduct.π f x) 0, zero_comp]

end Biproduct

/-! ### Shifted objects, truncations and cohomology -/

universe w w'

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory.{w'} C]

/-- `Hⁱ` of the object `X` placed in degree `n` vanishes for `i ≠ n`. -/
theorem isZero_homology_singleFunctor_obj (X : C) {i n : ℤ} (h : i ≠ n) :
    IsZero ((homologyFunctor C i).obj ((singleFunctor C n).obj X)) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact isZero_of_isGE _ n i h
  · exact isZero_of_isLE _ n i h

/-- **An object concentrated in one degree** is its cohomology placed in that degree:
`K.IsGE n` and `K.IsLE n` give `K ≅ (Hⁿ K)[-n]`. -/
theorem nonempty_iso_singleFunctor_homology (K : DerivedCategory C) (n : ℤ) [K.IsGE n]
    [K.IsLE n] : Nonempty (K ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K)) := by
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE K n
  exact ⟨e ≪≫ (singleFunctor C n).mapIso
    (((singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫ (homologyFunctor C n).mapIso e.symm)⟩

/-- **The truncation `τ_{< n}` keeps cohomology below `n`:** `Hⁱ (τ_{< n} K) ⟶ Hⁱ K` is an
isomorphism for `i < n`. -/
theorem isIso_homologyMap_truncLTι (K : DerivedCategory C) {i n : ℤ} (h : i < n) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLTι n).app K)) := by
  let T := (TStructure.t.triangleLTGE n).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished n K
  have h₃ : ∀ q, q < n → IsZero ((homologyFunctor C q).obj T.obj₃) := fun q hq =>
    isZero_of_isGE T.obj₃ n q hq
  have : Mono ((homologyFunctor C i).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by lia)).2
      ((h₃ (i - 1) (by lia)).eq_of_src _ _)
  have : Epi ((homologyFunctor C i).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 ((h₃ i h).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((homologyFunctor C i).map T.mor₁)

/-- **The truncation `τ_{≥ n}` keeps cohomology from `n` on:** `Hⁱ K ⟶ Hⁱ (τ_{≥ n} K)` is an
isomorphism for `n ≤ i`. -/
theorem isIso_homologyMap_truncGEπ (K : DerivedCategory C) {i n : ℤ} (h : n ≤ i) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ n).app K)) := by
  let T := (TStructure.t.triangleLTGE n).obj K
  have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished n K
  have h₁ : ∀ q, n - 1 < q → IsZero ((homologyFunctor C q).obj T.obj₁) := fun q hq =>
    isZero_of_isLE T.obj₁ (n - 1) q hq
  have : Mono ((homologyFunctor C i).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT i).2 ((h₁ i (by lia)).eq_of_src _ _)
  have : Epi ((homologyFunctor C i).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1)).2
      ((h₁ (i + 1) (by lia)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((homologyFunctor C i).map T.mor₂)

/-! ### Morphisms between shifted objects and `Ext` -/

/-- **Morphisms between shifted objects are `Ext` classes.** A morphism `X[-a] ⟶ Y[-b]` in the
derived category vanishes when `Ext^n(X, Y) = 0` for `n = a - b`. -/
theorem singleFunctor_hom_eq_zero_of_ext [HasExt.{w} C] {X Y : C} {a b : ℤ} {n : ℕ}
    (hn : (n : ℤ) = a - b) (h : ∀ e : Ext X Y n, e = 0)
    (f : (singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) : f = 0 := by
  let S := singleFunctors C
  let g : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) :=
    (S.shiftIso a 0 a (add_zero a)).inv.app X ≫ f⟦a⟧' ≫
      (S.shiftIso a (b - a) b (by lia)).hom.app Y ≫
        (S.shiftIso (n : ℤ) (b - a) 0 (by lia)).inv.app Y
  have hg : g = 0 := by
    have : g = (Ext.homEquiv (Ext.homEquiv.symm g : Ext X Y n)) := (Equiv.apply_symm_apply _ _).symm
    rw [this, h (Ext.homEquiv.symm g)]
    exact Ext.zero_hom X Y n
  have hf : f⟦a⟧' = 0 := by
    simpa only [g, Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero]
      using hg
  exact (shiftFunctor _ a).map_injective (by rw [hf, Functor.map_zero])

/-- A morphism `X[-j] ⟶ Y[-i][1]` vanishes when its transport along isomorphisms `X ≅ X'`,
`Y ≅ Y'` does for all such morphisms. -/
private theorem shift_hom_eq_zero_of_iso {i j : ℤ} {X X' Y Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : ∀ f : (singleFunctor C j).obj X' ⟶ ((singleFunctor C i).obj Y')⟦(1 : ℤ)⟧, f = 0)
    (f : (singleFunctor C j).obj X ⟶ ((singleFunctor C i).obj Y)⟦(1 : ℤ)⟧) : f = 0 := by
  have := h ((singleFunctor C j).map eX.inv ≫ f ≫ ((singleFunctor C i).map eY.hom)⟦(1 : ℤ)⟧')
  rwa [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero] at this

/-- `Finset.Icc a b` is `Finset.Icc a (b - 1)` with `b` inserted, for `a ≤ b`. -/
private theorem insert_Icc_sub_one {a b : ℤ} (h : a ≤ b) :
    insert b (Finset.Icc a (b - 1)) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  lia

/-- The induction behind `exists_iso_biproduct_homology`, with the vanishing hypothesis on
morphisms `(Hʲ K)[-j] ⟶ (Hⁱ K)[-i][1]` in the derived category, by induction on a bound `d` for
the length of `[a, b]`. -/
private theorem exists_iso_biproduct_aux (a : ℤ) (d : ℕ) :
    ∀ (b : ℤ), b < a + d → ∀ (K : DerivedCategory C) [K.IsGE a] [K.IsLE b],
      (∀ i j : ℤ, a ≤ i → i < j → j ≤ b →
        ∀ f : (singleFunctor C j).obj ((homologyFunctor C j).obj K) ⟶
          ((singleFunctor C i).obj ((homologyFunctor C i).obj K))⟦(1 : ℤ)⟧, f = 0) →
      Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
        (singleFunctor C i).obj ((homologyFunctor C i).obj K)) := by
  induction d with
  | zero =>
    intro b hb K _ _ _
    have hK : IsZero K := TStructure.t.isZero K b a (by lia)
    refine ⟨hK.iso (isZero_biproduct_of_isZero _ fun x => ?_)⟩
    have := Finset.mem_Icc.1 x.2
    lia
  | succ d ih =>
    intro b hb K _ _ hK
    by_cases hbd : b < a + d
    · exact ih b hbd K hK
    have hab : a ≤ b := by lia
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : T ∈ distTriang _ := TStructure.t.triangleLTGE_distinguished b K
    let A := T.obj₁
    let B := T.obj₃
    have : A.IsGE a := by change ((TStructure.t.truncLT b).obj K).IsGE a; infer_instance
    have : B.IsLE b := by change ((TStructure.t.truncGE b).obj K).IsLE b; infer_instance
    have : B.IsGE b := by change ((TStructure.t.truncGE b).obj K).IsGE b; infer_instance
    have hA : ∀ i, i < b → IsIso ((homologyFunctor C i).map T.mor₁) := fun i hi =>
      isIso_homologyMap_truncLTι K hi
    have hB : IsIso ((homologyFunctor C b).map T.mor₂) := isIso_homologyMap_truncGEπ K le_rfl
    let eH : ∀ i, i < b → ((homologyFunctor C i).obj A ≅ (homologyFunctor C i).obj K) :=
      fun i hi => @asIso _ _ _ _ ((homologyFunctor C i).map T.mor₁) (hA i hi)
    let eHB : (homologyFunctor C b).obj K ≅ (homologyFunctor C b).obj B :=
      @asIso _ _ _ _ ((homologyFunctor C b).map T.mor₂) hB
    obtain ⟨eA⟩ := ih (b - 1) (by lia) A fun i j hai hij hjb =>
      shift_hom_eq_zero_of_iso (eH j (by lia)) (eH i (by lia)) (hK i j hai hij (by lia))
    obtain ⟨eB⟩ := nonempty_iso_singleFunctor_homology B b
    have hmor₃ : T.mor₃ = 0 := by
      let g := eB.inv ≫ T.mor₃ ≫ eA.hom⟦(1 : ℤ)⟧'
      have hg : g = 0 := by
        have hπ : ∀ x : Finset.Icc a (b - 1), g ≫ (biproduct.π _ x)⟦(1 : ℤ)⟧' = 0 := by
          intro x
          have hx := Finset.mem_Icc.1 x.2
          exact shift_hom_eq_zero_of_iso eHB.symm (eH x (by lia))
            (hK x b hx.1 (by lia) le_rfl) _
        rw [← Category.comp_id g, ← CategoryTheory.Functor.map_id, ← biproduct.total,
          CategoryTheory.Functor.map_sum, Preadditive.comp_sum]
        exact Finset.sum_eq_zero fun x _ => by
          rw [Functor.map_comp, reassoc_of% (hπ x), zero_comp]
      have : T.mor₃ = eB.hom ≫ g ≫ eA.inv⟦(1 : ℤ)⟧' := by
        simp only [g, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Iso.hom_inv_id_assoc]
        rw [CategoryTheory.Functor.map_id, Category.comp_id]
      rw [this, hg, zero_comp, comp_zero]
    obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hmor₃
    let f : ℤ → DerivedCategory C := fun i => (singleFunctor C i).obj ((homologyFunctor C i).obj K)
    have hb' : b ∉ Finset.Icc a (b - 1) := by simp
    have key : Nonempty (K ≅ ⨁ fun i : (insert b (Finset.Icc a (b - 1)) : Finset ℤ) => f i) :=
      ⟨e ≪≫ biprod.mapIso
          (eA ≪≫ biproduct.mapIso fun i =>
            (singleFunctor C i).mapIso (eH i (by have := Finset.mem_Icc.1 i.2; lia)))
          (eB ≪≫ (singleFunctor C b).mapIso eHB.symm) ≪≫
        biproductInsertIso f hb'⟩
    rwa [insert_Icc_sub_one hab] at key

/-- **Hereditary splitting.** Let `K` be an object of the derived category of an abelian category
`C` with cohomology in degrees `[a, b]` (`K.IsGE a`, `K.IsLE b`). If
`Ext^{j - i + 1}(Hʲ K, Hⁱ K) = 0` for all degrees `a ≤ i < j ≤ b`, then `K` is isomorphic to the
direct sum of its shifted cohomology objects, `K ≅ ⨁_{i ∈ [a, b]} (Hⁱ K)[-i]`. -/
theorem exists_iso_biproduct_homology [HasExt.{w} C] (K : DerivedCategory C) (a b : ℤ)
    [K.IsGE a] [K.IsLE b]
    (hK : ∀ i j : ℤ, a ≤ i → i < j → j ≤ b → ∀ n : ℕ, (n : ℤ) = j - i + 1 →
      ∀ e : Ext ((homologyFunctor C j).obj K) ((homologyFunctor C i).obj K) n, e = 0) :
    Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
      (singleFunctor C i).obj ((homologyFunctor C i).obj K)) := by
  refine exists_iso_biproduct_aux a (b - a + 1).toNat b (by lia) K fun i j hai hij hjb f => ?_
  have h := singleFunctor_hom_eq_zero_of_ext (a := j) (b := i - 1) (n := (j - i + 1).toNat)
    (by lia) (hK i j hai hij hjb _ (by lia))
    (f ≫ ((singleFunctors C).shiftIso 1 (i - 1) i (by lia)).hom.app _)
  rwa [Preadditive.IsIso.comp_right_eq_zero] at h

/-- **Hereditary splitting, blanket form.** If `Ext^n(Hʲ K, Hⁱ K) = 0` for all degrees `i`, `j`
and all `n ≥ 2` (for instance when `C` has global dimension at most one), every `K` with
cohomology in `[a, b]` is `⨁_{i ∈ [a, b]} (Hⁱ K)[-i]`. -/
theorem exists_iso_biproduct_homology_of_two_le [HasExt.{w} C] (K : DerivedCategory C)
    (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ (i j : ℤ) (n : ℕ), 2 ≤ n →
      ∀ e : Ext ((homologyFunctor C j).obj K) ((homologyFunctor C i).obj K) n, e = 0) :
    Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
      (singleFunctor C i).obj ((homologyFunctor C i).obj K)) :=
  exists_iso_biproduct_homology K a b fun i j _ hij _ n hn => hK i j n (by lia)

/-! ### Cohomology of a sum of shifted objects -/

/-- **Cohomology of a sum of shifted objects, in a degree of the sum.** For a finite set `S` of
degrees, objects `X x` and `i ∈ S`, `Hⁱ (⨁_{x ∈ S} (X x)[-x]) ≅ X i`: `Hⁱ` preserves the
biproduct, the summands of degree `x ≠ i` have zero `Hⁱ`, and `Hⁱ (X i)[-i] ≅ X i`. -/
noncomputable def homologyBiproductSingleIso (S : Finset ℤ) (X : ℤ → C) {i : ℤ} (hi : i ∈ S) :
    (homologyFunctor C i).obj (⨁ fun x : S => (singleFunctor C x).obj (X x)) ≅ X i :=
  (homologyFunctor C i).mapBiproduct _ ≪≫
    biproductIsoOfIsZero (fun x : S => (homologyFunctor C i).obj ((singleFunctor C x).obj (X x)))
      ⟨i, hi⟩ (fun _ hx => isZero_homology_singleFunctor_obj _ fun h => hx (Subtype.ext h.symm)) ≪≫
    (singleFunctorCompHomologyFunctorIso C i).app (X i)

/-- **Cohomology of a sum of shifted objects, outside its degrees.** For `i ∉ S`,
`Hⁱ (⨁_{x ∈ S} (X x)[-x]) = 0`. -/
theorem isZero_homology_biproduct_single (S : Finset ℤ) (X : ℤ → C) {i : ℤ} (hi : i ∉ S) :
    IsZero ((homologyFunctor C i).obj (⨁ fun x : S => (singleFunctor C x).obj (X x))) :=
  (isZero_biproduct_of_isZero
    (fun x : S => (homologyFunctor C i).obj ((singleFunctor C x).obj (X x))) fun x =>
    isZero_homology_singleFunctor_obj _ fun h : i = (x : ℤ) => hi (by rw [h]; exact x.2)).of_iso
    ((homologyFunctor C i).mapBiproduct _)

/-- **A decomposition into shifted objects determines its summands.** If
`K ≅ ⨁_{x ∈ S} (X x)[-x]`, then `X i ≅ Hⁱ K` for every `i ∈ S`. -/
theorem nonempty_iso_homology_of_iso_biproduct_single {K : DerivedCategory C} {S : Finset ℤ}
    {X : ℤ → C} (e : K ≅ ⨁ fun x : S => (singleFunctor C x).obj (X x)) {i : ℤ} (hi : i ∈ S) :
    Nonempty (X i ≅ (homologyFunctor C i).obj K) :=
  ⟨(homologyBiproductSingleIso S X hi).symm ≪≫ (homologyFunctor C i).mapIso e.symm⟩

/-- **Uniqueness of the summands degree by degree.** If
`⨁_{x ∈ S} (X x)[-x] ≅ ⨁_{x ∈ S} (Y x)[-x]`, then `X i ≅ Y i` for every `i ∈ S`. -/
theorem nonempty_iso_of_iso_biproduct_single {S : Finset ℤ} {X Y : ℤ → C}
    (e : (⨁ fun x : S => (singleFunctor C x).obj (X x)) ≅
      ⨁ fun x : S => (singleFunctor C x).obj (Y x)) {i : ℤ} (hi : i ∈ S) :
    Nonempty (X i ≅ Y i) :=
  ⟨(homologyBiproductSingleIso S X hi).symm ≪≫ (homologyFunctor C i).mapIso e ≪≫
    homologyBiproductSingleIso S Y hi⟩

end TDA.Sheaf
