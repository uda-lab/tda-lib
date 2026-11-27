import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import TDA.Sheaf.BandIntervalDegreeOne
import TDA.Sheaf.RealConstructibleRefinement

/-!
# Convolution of real interval sheaves

The graded barcode of an interval sheaf after band convolution has one bar in degree zero
or one bar in degree one, given by the nonempty output set in that degree. In the
bounded-below derived category, the output is the corresponding interval sheaf placed in
that degree. For a finite sum of interval sheaves, the graded barcodes add as multisets.
-/

noncomputable section

open CategoryTheory Limits ZeroObject DerivedCategory TDA.Persistence

namespace TDA.Sheaf.BandConvolution

open RealStratification RealConstructible AlternatingDiagram

variable {k : Type} [Field k] {m : ℕ} {p : Fin m → ℝ}

private def intervalSumAppendIso {r : ℕ} (o : Fin r → Bool)
    (xs ys : List (FiniteInterval (r + 1))) :
    intervalSum (k := k) o (xs ++ ys) ≅ intervalSum o xs ⊞ intervalSum o ys := by
  induction xs with
  | nil => exact (isoZeroBiprod (isZero_zero _))
  | cons J xs ih =>
    exact biprod.mapIso (Iso.refl _) ih ≪≫ (biprod.associator _ _ _).symm

private theorem barcode_biprod {r : ℕ} {o : Fin r → Bool} (M N : Diagram k o)
    [∀ x, FiniteDimensional k (M.obj x)] [∀ x, FiniteDimensional k (N.obj x)]
    [∀ x, FiniteDimensional k ((M ⊞ N).obj x)] :
    barcode (M ⊞ N) = barcode M + barcode N := by
  let xs := (barcode M).toList
  let ys := (barcode N).toList
  have e : M ⊞ N ≅ intervalSum o (xs ++ ys) :=
    biprod.mapIso (barcodeIso M) (barcodeIso N) ≪≫ (intervalSumAppendIso o xs ys).symm
  simpa only [← Multiset.coe_add, xs, ys, Multiset.coe_toList] using
    barcode_eq_of_iso_intervalSum (M ⊞ N) e

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]

local notation "ISh[" k "," hp "," J "]" => Functor.obj (extension k hp) (interval _ J)
local notation "Conv[" ε "," F "]" => Functor.obj (T k ε) (Functor.obj (Plus.singleFunctor _ 0) F)
local notation "H[" ε "," F "," i "]" => Functor.obj (Plus.homologyFunctor _ i) (Conv[ε,F])

private theorem nonempty_iso_single_of_homology
    {X : Plus (realLine.Sheaf (ModuleCat k))} {i : ℤ}
    (hz : ∀ j : ℤ, j ≠ i → IsZero ((Plus.homologyFunctor _ j).obj X)) :
    Nonempty (X ≅ (Plus.singleFunctor _ i).obj ((Plus.homologyFunctor _ i).obj X)) := by
  let : (Plus.ι.obj X).IsGE i := (DerivedCategory.isGE_iff _ _).2
    (fun j hj => hz j (ne_of_lt hj))
  let : (Plus.ι.obj X).IsLE i := (DerivedCategory.isLE_iff _ _).2
    (fun j hj => hz j (ne_of_gt hj))
  obtain ⟨e⟩ := nonempty_iso_singleFunctor_homology (Plus.ι.obj X) i
  exact ⟨Plus.ι.preimageIso (e ≪≫ ((Plus.singleFunctorιIso _ i).app _).symm)⟩

private theorem intervalSet_nonempty {n : ℕ} {q : Fin n → ℝ}
    (hq : StrictMono q) (K : FiniteInterval (2 * n + 1)) : (intervalSet q K).Nonempty := by
  let v : Fin (2 * n + 1) := ⟨K.birth, K.birth_lt_death.trans_le K.death_le_size⟩
  obtain ⟨x, hx⟩ := stratum_nonempty hq v
  exact ⟨x, (mem_intervalSet_iff_alive hx).2 ⟨le_rfl, K.birth_lt_death⟩⟩

private theorem gradedBarcodeSets_eq_singleton_of_homology {n : ℕ} {q : Fin n → ℝ}
    (hq : StrictMono q) (K : FiniteInterval (2 * n + 1))
    {L : DerivedCategory (realLine.Sheaf (ModuleCat k))}
    (hL : HasConstructibleCohomology k q L) (i : ℤ)
    (e : (homologyFunctor _ i).obj L ≅ ISh[k,hq,K]) :
    gradedBarcodeSets k hq L hL i = {intervalSet q K} := by
  have := finiteDimensional_sections k hq (hL i)
  have hb : gradedBarcode k hq L hL i = {K} :=
    (barcode_eq_of_iso' ((sections k q).mapIso e)).trans
      (barcode_sections_extension_interval k hq K)
  simp [gradedBarcodeSets, hb]

variable [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

variable (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) {ε : ℝ} (hε : 0 ≤ ε)

include hε

private theorem isZero_homology_T_interval (h₀ : outSet0 ε (intervalSet p J) = ∅)
    (h₁ : outSet1 ε (intervalSet p J) = ∅) (i : ℤ) :
    IsZero H[ε,ISh[k,hp,J],i] := by
  rcases eq_or_ne i 0 with rfl | h0
  · exact isZero_H0T_interval hp J hε h₀
  rcases eq_or_ne i 1 with rfl | h1
  · exact isZero_H1T_interval hp J hε h₁
  exact isZero_homology_T_single ε hε _ i (by omega)

/-- An interval with two empty output sets has zero convolution in the derived category. -/
theorem isZero_T_interval (h₀ : outSet0 ε (intervalSet p J) = ∅)
    (h₁ : outSet1 ε (intervalSet p J) = ∅) :
    IsZero Conv[ε,ISh[k,hp,J]] := by
  let X := Conv[ε,ISh[k,hp,J]]
  have : IsIso (0 : X ⟶ 0) := (Plus.isIso_iff _).2 fun i => by
    rw [Functor.map_zero]
    exact (isIsoZero_iff_source_target_isZero _ _).2
      ⟨isZero_homology_T_interval hp J hε h₀ h₁ i,
        (Plus.homologyFunctor _ i).map_isZero (isZero_zero _)⟩
  exact (isZero_zero _).of_iso (asIso (0 : X ⟶ 0))

variable {n : ℕ} {q : Fin n → ℝ} (hq : StrictMono q) (K : FiniteInterval (2 * n + 1))

/-- If the degree-zero output is realized by an interval, convolution is its sheaf in degree
zero. -/
theorem nonempty_iso_T_interval_zero (hK : intervalSet q K = outSet0 ε (intervalSet p J)) :
    Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hq,K]) := by
  have hn : (outSet0 ε (intervalSet p J)).Nonempty := hK ▸ intervalSet_nonempty hq K
  have he : outSet1 ε (intervalSet p J) = ∅ := Set.not_nonempty_iff_eq_empty.mp
    (fun h => by
      rw [outSet0_eq_empty_of_outSet1_nonempty hε (ordConnected_intervalSet hp J) h] at hn
      exact Set.not_nonempty_empty hn)
  obtain ⟨e⟩ := nonempty_iso_single_of_homology
      (X := Conv[ε,ISh[k,hp,J]]) (i := 0) (fun i h0 => by
    rcases eq_or_ne i 1 with rfl | h1
    · exact isZero_H1T_interval hp J hε he
    · exact isZero_homology_T_single ε hε _ i (by omega))
  obtain ⟨f⟩ := nonempty_iso_H0T_interval (k := k) hp J hε hq K hK
  exact ⟨e ≪≫ (Plus.singleFunctor _ 0).mapIso f⟩

/-- If the degree-one output is realized by an interval, convolution is its sheaf shifted
by minus one. -/
theorem nonempty_iso_T_interval_one (hK : intervalSet q K = outSet1 ε (intervalSet p J)) :
    Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 1).obj ISh[k,hq,K]) := by
  have hn : (outSet1 ε (intervalSet p J)).Nonempty := hK ▸ intervalSet_nonempty hq K
  have he := outSet0_eq_empty_of_outSet1_nonempty hε (ordConnected_intervalSet hp J) hn
  obtain ⟨e⟩ := nonempty_iso_single_of_homology
      (X := Conv[ε,ISh[k,hp,J]]) (i := 1) (fun i h1 => by
    rcases eq_or_ne i 0 with rfl | h0
    · exact isZero_H0T_interval hp J hε he
    · exact isZero_homology_T_single ε hε _ i (by omega))
  obtain ⟨f⟩ := nonempty_iso_H1T_interval (k := k) hp J hε hq K hK
  exact ⟨e ≪≫ (Plus.singleFunctor _ 1).mapIso f⟩

local notation "pε" => sortedBreakpoints (bandBreakpoints p ε)
local notation "hpε" => strictMono_sortedBreakpoints (bandBreakpoints p ε)
local notation "Bar[" ε "," F "," h "," i "]" =>
  gradedBarcodeSets k hpε (Plus.ι.obj Conv[ε,F]) h i

/-- A nonempty output is the interval sheaf of its output set on the shifted breakpoints,
placed in degree zero or one. -/
theorem exists_intervalSheaf_T
    (h : (outSet0 ε (intervalSet p J)).Nonempty ∨ (outSet1 ε (intervalSet p J)).Nonempty) :
    ∃ (i : ℤ) (K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1)),
      ((i = 0 ∧ intervalSet pε K = outSet0 ε (intervalSet p J)) ∨
        (i = 1 ∧ intervalSet pε K = outSet1 ε (intervalSet p J))) ∧
      Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ i).obj ISh[k,hpε,K]) := by
  rcases h with h | h
  · obtain ⟨K, hK⟩ := exists_intervalSet_outSet0 hp J hε h
    exact ⟨0, K, Or.inl ⟨rfl, hK⟩, nonempty_iso_T_interval_zero hp J hε hpε K hK⟩
  · obtain ⟨K, hK⟩ := exists_intervalSet_outSet1 hp J hε h
    exact ⟨1, K, Or.inr ⟨rfl, hK⟩, nonempty_iso_T_interval_one hp J hε hpε K hK⟩

open Classical in
/-- A nonempty output set contributes one bar in its degree. All other degrees have empty
barcode. -/
theorem gradedBarcodeSets_T_interval (i : ℤ) :
    Bar[ε,ISh[k,hp,J],hasConstructibleCohomology_T_interval hp J hε,i] =
      if i = 0 ∧ (outSet0 ε (intervalSet p J)).Nonempty then {outSet0 ε (intervalSet p J)}
      else if i = 1 ∧ (outSet1 ε (intervalSet p J)).Nonempty then {outSet1 ε (intervalSet p J)}
      else 0 := by
  classical
  rcases eq_or_ne i 0 with rfl | h0
  · simp only [zero_ne_one, false_and, ite_false, true_and]
    split_ifs with hn
    · obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_H0T (k := k) hp J hε hn
      rw [← hK]
      exact gradedBarcodeSets_eq_singleton_of_homology hpε K _ 0 e
    · unfold gradedBarcodeSets
      rw [gradedBarcode_eq_zero_of_isZero k hpε _
        (isZero_H0T_interval hp J hε (Set.not_nonempty_iff_eq_empty.mp hn)), Multiset.map_zero]
  rcases eq_or_ne i 1 with rfl | h1
  · simp only [h0, false_and, ite_false, true_and]
    split_ifs with hn
    · obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_H1T (k := k) hp J hε hn
      rw [← hK]
      exact gradedBarcodeSets_eq_singleton_of_homology hpε K _ 1 e
    · unfold gradedBarcodeSets
      rw [gradedBarcode_eq_zero_of_isZero k hpε _
        (isZero_H1T_interval hp J hε (Set.not_nonempty_iff_eq_empty.mp hn)), Multiset.map_zero]
  simp only [h0, h1, false_and, ite_false, gradedBarcodeSets]
  rw [gradedBarcode_eq_zero_of_isZero k hpε _
    (isZero_homology_T_single ε hε _ i (by omega)), Multiset.map_zero]


section Decomposition

/-- For a finite interval decomposition, the barcode after convolution is the multiset sum
of the convolved bars in each degree. Repeated input or output bars retain multiplicity. -/
theorem gradedBarcodeSets_T_decomposition {F : realLine.Sheaf (ModuleCat k)}
    (hF : IsConstructible (breakpoints p) F)
    (xs : List (FiniteInterval (2 * m + 1))) (e : F ≅ intervalSheafSum k hp xs) (i : ℤ) :
    Bar[ε,F,hasConstructibleCohomology_T hp hε hF,i] =
      (xs : Multiset _).bind (fun K =>
        Bar[ε,ISh[k,hp,K],hasConstructibleCohomology_T_interval hp K hε,i]) := by
  let G := Plus.singleFunctor (realLine.Sheaf (ModuleCat k)) 0 ⋙ T k ε ⋙ Plus.ι
  let B := G ⋙ homologyFunctor _ i ⋙ sections k pε
  have := preservesBinaryBiproducts_of_preservesBiproducts B
  have hsum (ys : List (FiniteInterval (2 * m + 1))) :
      HasConstructibleCohomology k pε (G.obj (intervalSheafSum k hp ys)) :=
    hasConstructibleCohomology_T hp hε (isConstructible_of_iso
      (extensionIntervalSumIso k hp ys) (isConstructible_extension k hp fun _ => inferInstance))
  change gradedBarcodeSets k hpε (G.obj F) (hasConstructibleCohomology_T hp hε hF) i = _
  rw [gradedBarcodeSets_eq_of_iso k hpε (G.mapIso e) _ (hsum xs)]
  clear e hF F
  induction xs with
  | nil =>
    have hz : IsZero ((homologyFunctor _ i).obj (G.obj (intervalSheafSum k hp []))) :=
      (G ⋙ homologyFunctor _ i).map_isZero (isZero_zero _)
    rw [Multiset.coe_nil, Multiset.zero_bind, gradedBarcodeSets,
      gradedBarcode_eq_zero_of_isZero k hpε _ hz, Multiset.map_zero]
  | cons K xs ih =>
    let A := B.obj (intervalSheafSum k hp (K :: xs))
    let M := B.obj ISh[k,hp,K]
    let N := B.obj (intervalSheafSum k hp xs)
    have hA : ∀ x, FiniteDimensional k (A.obj x) := finiteDimensional_sections k hpε (hsum _ i)
    have : ∀ x, FiniteDimensional k (N.obj x) := finiteDimensional_sections k hpε (hsum _ i)
    have : ∀ x, FiniteDimensional k (M.obj x) :=
      finiteDimensional_sections k hpε (hasConstructibleCohomology_T_interval hp K hε i)
    let eB : A ≅ M ⊞ N := B.mapBiprod _ _
    have (x : Paths (Vertex (orient (bandBreakpoints p ε).card))) :
        FiniteDimensional k ((M ⊞ N).obj x) := (eB.app x).toLinearEquiv.finiteDimensional
    have he : barcode A = barcode M + barcode N :=
      (barcode_eq_of_iso' eB).trans (barcode_biprod M N)
    change (barcode A).map (intervalSet pε) = (K ::ₘ (xs : Multiset _)).bind _
    rw [he, Multiset.map_add, Multiset.cons_bind, ← ih]
    rfl

end Decomposition

section Endpoints

private theorem exists_intervalSheaf_T_zero {A : Set ℝ}
    (hA : outSet0 ε (intervalSet p J) = A) (hne : A.Nonempty) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1), intervalSet pε K = A ∧
      Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) := by
  obtain ⟨K, hK⟩ := exists_intervalSet_outSet0 hp J hε (hA.symm ▸ hne)
  exact ⟨K, hK.trans hA, nonempty_iso_T_interval_zero hp J hε hpε K hK⟩

private theorem exists_intervalSheaf_T_one {A : Set ℝ}
    (hA : outSet1 ε (intervalSet p J) = A) (hne : A.Nonempty) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1), intervalSet pε K = A ∧
      Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 1).obj ISh[k,hpε,K]) := by
  obtain ⟨K, hK⟩ := exists_intervalSet_outSet1 hp J hε (hA.symm ▸ hne)
  exact ⟨K, hK.trans hA, nonempty_iso_T_interval_one hp J hε hpε K hK⟩

/-- A closed interval expands at both ends in degree zero. -/
theorem exists_intervalSheaf_T_Icc {a b : ℝ} (hab : a ≤ b)
    (hJ : intervalSet p J = Set.Icc a b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Icc (a - ε) (b + ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Icc hε hab)
    (Set.nonempty_Icc.mpr (by linarith))

/-- An interval closed on the left translates left in degree zero. -/
theorem exists_intervalSheaf_T_Ico {a b : ℝ} (hab : a < b)
    (hJ : intervalSet p J = Set.Ico a b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Ico (a - ε) (b - ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Ico hε hab)
    (Set.nonempty_Ico.mpr (by linarith))

/-- An interval closed on the right translates right in degree zero. -/
theorem exists_intervalSheaf_T_Ioc {a b : ℝ} (hab : a < b)
    (hJ : intervalSet p J = Set.Ioc a b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Ioc (a + ε) (b + ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Ioc hε hab)
    (Set.nonempty_Ioc.mpr (by linarith))

/-- Below the open-interval threshold, the interval shrinks at both ends in degree zero. -/
theorem exists_intervalSheaf_T_Ioo_below {a b : ℝ} (hab : a < b) (h : 2 * ε < b - a)
    (hJ : intervalSet p J = Set.Ioo a b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Ioo (a + ε) (b - ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Ioo hε hab)
    (Set.nonempty_Ioo.mpr (by linarith))

/-- At the open-interval threshold, convolution gives the midpoint sheaf in degree one. -/
theorem exists_intervalSheaf_T_Ioo_threshold {a b : ℝ} (hab : a < b) (h : 2 * ε = b - a)
    (hJ : intervalSet p J = Set.Ioo a b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = {(a + b) / 2} ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 1).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_one hp J hε (hJ ▸ outSet1_Ioo_threshold hε hab h)
    (Set.singleton_nonempty _)

/-- At the open-interval threshold the shifted augmentation represents a nonzero
`Ext¹` class from the midpoint sheaf to the open interval sheaf. -/
theorem exists_ext_one_aug_interval_Ioo_threshold
    [HasExt.{0} (realLine.Sheaf (ModuleCat k))]
    {a b : ℝ} (hab : a < b) (h : 2 * ε = b - a) (hJ : intervalSet p J = Set.Ioo a b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = {(a + b) / 2} ∧
      ∃ e : Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 1).obj ISh[k,hpε,K],
        ∃ ξ : Abelian.Ext ISh[k,hpε,K] ISh[k,hp,J] 1,
          ξ ≠ 0 ∧ ξ.hom =
            ((singleFunctors _).shiftIso 1 0 1 (add_zero 1)).inv.app ISh[k,hpε,K] ≫
              (shiftFunctor _ (1 : ℤ)).map (Plus.ι.map
                (e.inv ≫ (aug k hε).app ((Plus.singleFunctor _ 0).obj ISh[k,hp,J]))) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_T_Ioo_threshold (k := k) hp J hε hab h hJ
  let C := realLine.Sheaf (ModuleCat k)
  let F := ISh[k,hp,J]
  let G := ISh[k,hpε,K]
  let e₁ := ((singleFunctors C).shiftIso 1 0 1 (add_zero 1)).app G
  let u := (aug k hε).app ((Plus.singleFunctor C 0).obj F)
  let v : (singleFunctor C 0).obj G ⟶ ((singleFunctor C 0).obj F)⟦(1 : ℤ)⟧ :=
    e₁.inv ≫ (shiftFunctor _ (1 : ℤ)).map (Plus.ι.map (e.inv ≫ u))
  refine ⟨K, hK, e, (Abelian.Ext.homEquiv (n := 1)).symm v, ?_, Equiv.apply_symm_apply _ _⟩
  intro hz
  have hv : v = 0 := by
    have he := congrArg (Abelian.Ext.homEquiv (n := 1)) hz
    rw [Equiv.apply_symm_apply] at he
    exact he.trans (Abelian.Ext.zero_hom G F 1)
  have hs : (shiftFunctor _ (1 : ℤ)).map (Plus.ι.map (e.inv ≫ u)) = 0 :=
    (Preadditive.IsIso.comp_left_eq_zero e₁.inv _).mp hv
  have hi : Plus.ι.map (e.inv ≫ u) = 0 :=
    (shiftFunctor _ (1 : ℤ)).map_injective
      (hs.trans ((shiftFunctor _ (1 : ℤ)).map_zero _ _).symm)
  have hu : e.inv ≫ u = 0 := Plus.ι.map_injective (hi.trans (Plus.ι.map_zero _ _).symm)
  exact aug_interval_Ioo_threshold_ne_zero (k := k) hp J hε hab h hJ
    ((Preadditive.IsIso.comp_left_eq_zero _ _).mp hu)

/-- Above the open-interval threshold, convolution gives a closed interval in degree one. -/
theorem exists_intervalSheaf_T_Ioo_above {a b : ℝ} (hab : a < b) (h : b - a < 2 * ε)
    (hJ : intervalSet p J = Set.Ioo a b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Icc (b - ε) (a + ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 1).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_one hp J hε (hJ ▸ outSet1_Ioo hε hab)
    (Set.nonempty_Icc.mpr (by linarith))

/-- A closed right ray expands to the left in degree zero. -/
theorem exists_intervalSheaf_T_Ici {a : ℝ}
    (hJ : intervalSet p J = Set.Ici a) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Ici (a - ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Ici hε a)
    ⟨a - ε, Set.mem_Ici.mpr le_rfl⟩

/-- A closed left ray expands to the right in degree zero. -/
theorem exists_intervalSheaf_T_Iic {b : ℝ}
    (hJ : intervalSet p J = Set.Iic b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Iic (b + ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Iic hε b)
    ⟨b + ε, Set.mem_Iic.mpr le_rfl⟩

/-- An open right ray shrinks from the left in degree zero. -/
theorem exists_intervalSheaf_T_Ioi {a : ℝ}
    (hJ : intervalSet p J = Set.Ioi a) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Ioi (a + ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Ioi hε a) (Set.nonempty_Ioi)

/-- An open left ray shrinks from the right in degree zero. -/
theorem exists_intervalSheaf_T_Iio {b : ℝ}
    (hJ : intervalSet p J = Set.Iio b) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Iio (b - ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_Iio hε b) (Set.nonempty_Iio)

/-- The full line stays in degree zero with the same support. -/
theorem exists_intervalSheaf_T_univ (hJ : intervalSet p J = Set.univ) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.univ ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_univ hε) (Set.univ_nonempty)

/-- A point expands to a closed interval in degree zero. -/
theorem exists_intervalSheaf_T_singleton {a : ℝ}
    (hJ : intervalSet p J = {a}) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet pε K = Set.Icc (a - ε) (a + ε) ∧
        Nonempty (Conv[ε,ISh[k,hp,J]] ≅ (Plus.singleFunctor _ 0).obj ISh[k,hpε,K]) :=
  exists_intervalSheaf_T_zero hp J hε (hJ ▸ outSet0_singleton hε a)
    (Set.nonempty_Icc.mpr (by linarith))

end Endpoints

end TDA.Sheaf.BandConvolution
