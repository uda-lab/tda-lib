import TDA.Sheaf.RealConstructibleExt
import TDA.Sheaf.AlternatingDecomposition
import TDA.Sheaf.HereditarySplitting

/-!
# Bounded complexes with constructible cohomology on the real line

Fix strictly increasing breakpoints `p : Fin m → ℝ` (`hp : StrictMono p`) and a field `k`; write
`Φ = extension k hp` and `Γ = sections k p` (`TDA.Sheaf.RealConstructible`). Objects `K` live in
Mathlib's derived category `DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)` of all
sheaves of `k`-modules on `ℝ`, for an instance `HasDerivedCategory`, with `Hⁱ K` its cohomology
sheaves and `F[-i] = (singleFunctor _ i).obj F`. Boundedness is that of the canonical
t-structure (`K.IsGE a`, `K.IsLE b`).

* `HasConstructibleCohomology k p K`: every cohomology sheaf `Hⁱ K` is constructible for the
  breakpoints of `p` (D1's `IsConstructible`); it is invariant under isomorphism
  (`HasConstructibleCohomology.of_iso`) and monotone in the breakpoints
  (`HasConstructibleCohomology.mono`). `hasConstructibleCohomology_of_isConstructible`: cohomology
  sheaves constructible for their own breakpoint sets, finitely many nonzero, give constructible
  cohomology for any `p` whose breakpoints contain all of these sets.
* `exists_iso_biproduct_homology_of_constructible`: such a `K` with cohomology in `[a, b]` is
  `⨁_{i ∈ [a, b]} (Hⁱ K)[-i]`. This is `exists_iso_biproduct_homology_of_two_le` with the
  vanishing `Ext^{≥ 2}` between constructible sheaves (`ext_constructible_eq_zero_of_two_le`).
* `gradedBarcode k hp K hK i`: D2's barcode of the diagram `Γ (Hⁱ K)` of the degree-`i`
  cohomology sheaf, a multiset of intervals `FiniteInterval (2 * m + 1)` of the strata path.
  `gradedBarcode_eq_of_iso`: isomorphic objects have equal graded barcodes in every degree;
  `gradedBarcode_eq_zero_of_isZero` and its consequences outside `[a, b]`.
* `intervalSheafSum k hp xs`: the iterated biproduct `⊞_{J ∈ xs} Φ (interval J)` of the interval
  sheaves of a list of intervals, with `extensionIntervalSumIso : Φ (intervalSum xs) ≅
  intervalSheafSum k hp xs`; `barcodeSheaf k hp B = intervalSheafSum k hp B.toList` for a multiset
  `B`, and `barcode_sections_barcodeSheaf : barcode (Γ (barcodeSheaf B)) = B`.
* `exists_iso_biproduct_barcodeSheaf`, the decomposition: `K ≅ ⨁_{i ∈ [a, b]} ⨁_{J ∈ Bᵢ}
  (Φ (interval J))[-i]` with `Bᵢ = gradedBarcode k hp K hK i`, that is
  `K ≅ ⨁_{i ∈ [a, b]} (barcodeSheaf k hp Bᵢ)[-i]`.
* `gradedBarcode_eq_of_iso_biproduct`, uniqueness: if `K ≅ ⨁_{x ∈ S} (barcodeSheaf k hp (B x))[-x]`
  for a finite set `S` of degrees and multisets `B x`, then `gradedBarcode k hp K hK i = B i` for
  `i ∈ S` (and `= 0` for `i ∉ S`). `gradedBarcode_biproduct` computes the graded barcode of such a
  sum; `hasConstructibleCohomology_biproduct` and `hasConstructibleCohomology_singleFunctor` give
  constructibility of its cohomology and of a constructible sheaf placed in one degree, and
  `gradedBarcode_singleFunctor` computes the graded barcode of the latter.

Constructibility uses the interval-local `IsLocallyConstantOn`; its intended equivalence with
"locally isomorphic to a constant sheaf" is not yet proved in Lean (#1250).
-/

open CategoryTheory Limits ZeroObject DerivedCategory TDA.Persistence
  TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealStratification

namespace TDA.Sheaf.RealConstructible

universe w

variable (k : Type) [Field k] {m : ℕ} {p : Fin m → ℝ}

/-! ### Interval sheaves of a barcode -/

/-- The sheaf of a list `xs` of intervals of the strata path: the iterated biproduct
`⊞_{J ∈ xs} Φ (interval J)` of the interval sheaves, `0` for the empty list. -/
noncomputable def intervalSheafSum (hp : StrictMono p) :
    List (FiniteInterval (2 * m + 1)) → TopCat.Sheaf (ModuleCat.{0} k) realLine
  | [] => 0
  | J :: xs => (extension k hp).obj (interval (orient m) J) ⊞ intervalSheafSum hp xs

@[simp]
theorem intervalSheafSum_nil (hp : StrictMono p) : intervalSheafSum k hp [] = 0 := rfl

@[simp]
theorem intervalSheafSum_cons (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    (xs : List (FiniteInterval (2 * m + 1))) :
    intervalSheafSum k hp (J :: xs) =
      ((extension k hp).obj (interval (orient m) J) ⊞ intervalSheafSum k hp xs) := rfl

/-- `Φ` of an interval sum of diagrams is the interval sum of the interval sheaves: `Φ` is
additive. -/
noncomputable def extensionIntervalSumIso (hp : StrictMono p)
    (xs : List (FiniteInterval (2 * m + 1))) :
    (extension k hp).obj (intervalSum (orient m) xs) ≅ intervalSheafSum k hp xs := by
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (extension k hp)
  induction xs with
  | nil => exact (extension k hp).mapZeroObject
  | cons J xs ih => exact (extension k hp).mapBiprod _ _ ≪≫ biprod.mapIso (Iso.refl _) ih

/-- The sheaf of a barcode `B`: the interval sum `⊞_{J ∈ B} Φ (interval J)` over the list
representative of `B` used by D2's `barcodeDiagram`. -/
noncomputable def barcodeSheaf (hp : StrictMono p) (B : Multiset (FiniteInterval (2 * m + 1))) :
    TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  intervalSheafSum k hp B.toList

/-- `Φ (barcodeDiagram B) ≅ barcodeSheaf B`. -/
noncomputable def extensionBarcodeDiagramIso (hp : StrictMono p)
    (B : Multiset (FiniteInterval (2 * m + 1))) :
    (extension k hp).obj (barcodeDiagram (orient m) B) ≅ barcodeSheaf k hp B :=
  extensionIntervalSumIso k hp B.toList

/-- The sheaf of a barcode is constructible. -/
theorem isConstructible_barcodeSheaf (hp : StrictMono p)
    (B : Multiset (FiniteInterval (2 * m + 1))) :
    IsConstructible (breakpoints p) (barcodeSheaf k hp B) :=
  isConstructible_of_iso (extensionBarcodeDiagramIso k hp B)
    (isConstructible_extension k hp fun _ => inferInstance)

/-- The sections of the sheaf of a barcode over the stars are finite-dimensional, so
`barcode ((sections k p).obj (barcodeSheaf k hp B))` elaborates without a local instance. -/
instance finiteDimensional_sections_barcodeSheaf (hp : StrictMono p)
    (B : Multiset (FiniteInterval (2 * m + 1))) (X : Paths (Vertex (orient m))) :
    FiniteDimensional k (((sections k p).obj (barcodeSheaf k hp B)).obj X) :=
  finiteDimensional_sections k hp (isConstructible_barcodeSheaf k hp B) X

/-- **The barcode of the sheaf of a barcode** `B` is `B`: `Γ (barcodeSheaf B) ≅ barcodeDiagram B`
through D1's counit. -/
theorem barcode_sections_barcodeSheaf (hp : StrictMono p)
    (B : Multiset (FiniteInterval (2 * m + 1))) :
    barcode ((sections k p).obj (barcodeSheaf k hp B)) = B :=
  barcode_eq_of_iso _ ((sections k p).mapIso (extensionBarcodeDiagramIso k hp B).symm ≪≫
    (extensionSectionsIso k hp).app _)

/-- A sheaf with a single interval sheaf: `barcode (Γ (Φ (interval J))) = {J}`. -/
theorem barcode_sections_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    barcode ((sections k p).obj ((extension k hp).obj (interval (orient m) J))) = {J} :=
  barcode_eq_of_iso_intervalSum _ (xs := [J])
    ((extensionSectionsIso k hp).app (interval (orient m) J) ≪≫ isoBiprodZero (isZero_zero _))

/-- A zero sheaf is constructible. -/
theorem isConstructible_of_isZero (hp : StrictMono p)
    {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} (hF : IsZero F) :
    IsConstructible (breakpoints p) F :=
  isConstructible_of_iso (((extension k hp).map_isZero (isZero_zero _)).iso hF)
    (isConstructible_extension k hp fun _ => inferInstance)

/-! ### Constructible cohomology -/

variable [HasDerivedCategory.{w} (TopCat.Sheaf (ModuleCat.{0} k) realLine)]

/-- An object `K` of the derived category of sheaves of `k`-modules on `ℝ` **has constructible
cohomology** for the breakpoints of `p` when every cohomology sheaf `Hⁱ K` is constructible for
them. -/
def HasConstructibleCohomology (p : Fin m → ℝ)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)) : Prop :=
  ∀ i : ℤ, IsConstructible (breakpoints p) ((homologyFunctor _ i).obj K)

variable {k}

/-- Constructible cohomology is invariant under isomorphism. -/
theorem HasConstructibleCohomology.of_iso
    {K L : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)} (e : K ≅ L)
    (hK : HasConstructibleCohomology k p K) : HasConstructibleCohomology k p L :=
  fun i => isConstructible_of_iso ((homologyFunctor _ i).mapIso e) (hK i)

/-- **Constructible cohomology is monotone in the breakpoints**: if the breakpoints of `p` are
among those of `q`, cohomology constructible for `p` is constructible for `q`. -/
theorem HasConstructibleCohomology.mono {m' : ℕ} {q : Fin m' → ℝ}
    (hpq : breakpoints p ⊆ breakpoints q)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)}
    (hK : HasConstructibleCohomology k p K) : HasConstructibleCohomology k q K :=
  fun i => (hK i).mono hpq

variable (k)

/-- A constructible sheaf placed in one degree has constructible cohomology. -/
theorem hasConstructibleCohomology_singleFunctor (hp : StrictMono p)
    {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} (hF : IsConstructible (breakpoints p) F)
    (n : ℤ) : HasConstructibleCohomology k p ((singleFunctor _ n).obj F) := fun i => by
  by_cases h : i = n
  · subst h
    exact isConstructible_of_iso ((singleFunctorCompHomologyFunctorIso _ i).app F).symm hF
  · exact isConstructible_of_isZero k hp (isZero_homology_singleFunctor_obj F h)

/-- A finite sum of barcode sheaves placed in distinct degrees has constructible cohomology. -/
theorem hasConstructibleCohomology_biproduct (hp : StrictMono p) (S : Finset ℤ)
    (B : ℤ → Multiset (FiniteInterval (2 * m + 1))) :
    HasConstructibleCohomology k p
      (⨁ fun x : S => (singleFunctor _ x).obj (barcodeSheaf k hp (B x))) := fun i => by
  by_cases hi : i ∈ S
  · exact isConstructible_of_iso
      (homologyBiproductSingleIso S (fun x => barcodeSheaf k hp (B x)) hi).symm
      (isConstructible_barcodeSheaf k hp (B i))
  · exact isConstructible_of_isZero k hp
      (isZero_homology_biproduct_single S (fun x => barcodeSheaf k hp (B x)) hi)

/-- **Breakpoints per degree.** If the cohomology of `K` vanishes outside a finite set `T` of
degrees and every `Hⁱ K` with `i ∈ T` is constructible for its own finite set `S i`, contained in
the breakpoints of `p`, then `K` has constructible cohomology for the breakpoints of `p`. -/
theorem hasConstructibleCohomology_of_isConstructible (hp : StrictMono p)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)} (T : Finset ℤ)
    (S : ℤ → Finset ℝ) (hS : ∀ i ∈ T, S i ⊆ breakpoints p)
    (hK : ∀ i ∈ T, IsConstructible (S i) ((homologyFunctor _ i).obj K))
    (hz : ∀ i ∉ T, IsZero ((homologyFunctor _ i).obj K)) : HasConstructibleCohomology k p K :=
  fun i => by
    by_cases hi : i ∈ T
    · exact (hK i hi).mono (hS i hi)
    · exact isConstructible_of_isZero k hp (hz i hi)

/-- **Splitting.** An object of the derived category of sheaves of `k`-modules on `ℝ` with
cohomology in `[a, b]`, all constructible for the breakpoints of `p`, is the direct sum
`⨁_{i ∈ [a, b]} (Hⁱ K)[-i]` of its shifted cohomology sheaves. -/
theorem exists_iso_biproduct_homology_of_constructible (hp : StrictMono p)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)) (a b : ℤ) [K.IsGE a]
    [K.IsLE b] (hK : HasConstructibleCohomology k p K) :
    Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
      (singleFunctor _ i).obj ((homologyFunctor _ i).obj K)) := by
  have := hasExt_sheaf_realLine k
  exact exists_iso_biproduct_homology_of_two_le K a b fun i j _ hn e =>
    ext_constructible_eq_zero_of_two_le k hp ⟨_, hK j⟩ ⟨_, hK i⟩ hn e

/-! ### The graded barcode -/

/-- **The graded barcode.** For `K` with constructible cohomology and a degree `i`, the barcode
(D2) of the diagram `Γ (Hⁱ K)` of sections of the cohomology sheaf `Hⁱ K` over the stars: a
multiset of intervals of the strata path `orient m`. -/
noncomputable def gradedBarcode (hp : StrictMono p)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine))
    (hK : HasConstructibleCohomology k p K) (i : ℤ) : Multiset (FiniteInterval (2 * m + 1)) :=
  haveI := finiteDimensional_sections k hp (hK i)
  barcode ((sections k p).obj ((homologyFunctor _ i).obj K))

/-- The graded barcode in degree `i` is the multiset of any decomposition of `Γ (Hⁱ K)`. -/
theorem gradedBarcode_eq_of_iso_barcodeDiagram (hp : StrictMono p)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)}
    (hK : HasConstructibleCohomology k p K) {i : ℤ} {B : Multiset (FiniteInterval (2 * m + 1))}
    (e : (sections k p).obj ((homologyFunctor _ i).obj K) ≅ barcodeDiagram (orient m) B) :
    gradedBarcode k hp K hK i = B :=
  haveI := finiteDimensional_sections k hp (hK i)
  barcode_eq_of_iso _ e

/-- **Invariance.** Isomorphic objects have equal graded barcodes in every degree. -/
theorem gradedBarcode_eq_of_iso (hp : StrictMono p)
    {K L : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)} (e : K ≅ L)
    (hK : HasConstructibleCohomology k p K) (hL : HasConstructibleCohomology k p L) (i : ℤ) :
    gradedBarcode k hp K hK i = gradedBarcode k hp L hL i :=
  haveI := finiteDimensional_sections k hp (hK i)
  haveI := finiteDimensional_sections k hp (hL i)
  barcode_eq_of_iso' ((sections k p).mapIso ((homologyFunctor _ i).mapIso e))

/-- The graded barcode vanishes in a degree where the cohomology sheaf is zero. -/
theorem gradedBarcode_eq_zero_of_isZero (hp : StrictMono p)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)}
    (hK : HasConstructibleCohomology k p K) {i : ℤ} (h : IsZero ((homologyFunctor _ i).obj K)) :
    gradedBarcode k hp K hK i = 0 :=
  haveI := finiteDimensional_sections k hp (hK i)
  barcode_eq_zero_of_isZero _ ((sections k p).map_isZero h)

/-- The graded barcode vanishes below the degrees of `K`. -/
theorem gradedBarcode_eq_zero_of_lt (hp : StrictMono p)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)}
    (hK : HasConstructibleCohomology k p K) {a i : ℤ} [K.IsGE a] (h : i < a) :
    gradedBarcode k hp K hK i = 0 :=
  gradedBarcode_eq_zero_of_isZero k hp hK (isZero_of_isGE K a i h)

/-- The graded barcode vanishes above the degrees of `K`. -/
theorem gradedBarcode_eq_zero_of_gt (hp : StrictMono p)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)}
    (hK : HasConstructibleCohomology k p K) {b i : ℤ} [K.IsLE b] (h : b < i) :
    gradedBarcode k hp K hK i = 0 :=
  gradedBarcode_eq_zero_of_isZero k hp hK (isZero_of_isLE K b i h)

/-- **A constructible sheaf placed in degree `n`** has the barcode of `Γ F` in degree `n` and the
empty barcode in every other degree. -/
theorem gradedBarcode_singleFunctor (hp : StrictMono p)
    {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} (hF : IsConstructible (breakpoints p) F)
    (n i : ℤ) :
    gradedBarcode k hp ((singleFunctor _ n).obj F)
        (hasConstructibleCohomology_singleFunctor k hp hF n) i =
      if i = n then
        (haveI := finiteDimensional_sections k hp hF; barcode ((sections k p).obj F))
      else 0 := by
  have := finiteDimensional_sections k hp hF
  split_ifs with h
  · subst h
    have := finiteDimensional_sections k hp
      (hasConstructibleCohomology_singleFunctor k hp hF i i)
    exact barcode_eq_of_iso' ((sections k p).mapIso
      ((singleFunctorCompHomologyFunctorIso _ i).app F))
  · exact gradedBarcode_eq_zero_of_isZero k hp _ (isZero_homology_singleFunctor_obj F h)

/-- The cohomology sheaf in degree `i` is the sheaf of the degree-`i` graded barcode. -/
theorem nonempty_homology_iso_barcodeSheaf (hp : StrictMono p)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine))
    (hK : HasConstructibleCohomology k p K) (i : ℤ) :
    Nonempty ((homologyFunctor _ i).obj K ≅ barcodeSheaf k hp (gradedBarcode k hp K hK i)) := by
  have := finiteDimensional_sections k hp (hK i)
  exact ⟨(sectionsExtensionIso k hp).app ⟨_, hK i⟩ ≪≫
    (extension k hp).mapIso (barcodeIso ((sections k p).obj ((homologyFunctor _ i).obj K))) ≪≫
    extensionBarcodeDiagramIso k hp _⟩

/-- **The decomposition.** An object `K` of the derived category of sheaves of `k`-modules on `ℝ`
with cohomology in `[a, b]`, all constructible for the breakpoints of `p`, is the direct sum of
shifted interval sheaves given by its graded barcode:
`K ≅ ⨁_{i ∈ [a, b]} ⨁_{J ∈ gradedBarcode K i} (Φ (interval J))[-i]`, the inner sum being
`barcodeSheaf k hp (gradedBarcode k hp K hK i)`. -/
theorem exists_iso_biproduct_barcodeSheaf (hp : StrictMono p)
    (K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)) (a b : ℤ) [K.IsGE a]
    [K.IsLE b] (hK : HasConstructibleCohomology k p K) :
    Nonempty (K ≅ ⨁ fun i : Finset.Icc a b =>
      (singleFunctor _ i).obj (barcodeSheaf k hp (gradedBarcode k hp K hK i))) := by
  obtain ⟨e⟩ := exists_iso_biproduct_homology_of_constructible k hp K a b hK
  exact ⟨e ≪≫ biproduct.mapIso fun i =>
    (singleFunctor _ i).mapIso (nonempty_homology_iso_barcodeSheaf k hp K hK i).some⟩

/-- **Uniqueness of the decomposition.** If `K ≅ ⨁_{x ∈ S} (barcodeSheaf k hp (B x))[-x]` for a
finite set `S` of degrees and multisets `B x` of intervals, then the graded barcode of `K` in
every degree `i ∈ S` is `B i`. -/
theorem gradedBarcode_eq_of_iso_biproduct (hp : StrictMono p)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)}
    (hK : HasConstructibleCohomology k p K) {S : Finset ℤ}
    {B : ℤ → Multiset (FiniteInterval (2 * m + 1))}
    (e : K ≅ ⨁ fun x : S => (singleFunctor _ x).obj (barcodeSheaf k hp (B x))) {i : ℤ}
    (hi : i ∈ S) : gradedBarcode k hp K hK i = B i := by
  obtain ⟨f⟩ := nonempty_iso_homology_of_iso_biproduct_single
    (X := fun x => barcodeSheaf k hp (B x)) e hi
  exact gradedBarcode_eq_of_iso_barcodeDiagram k hp hK
    ((sections k p).mapIso (f.symm ≪≫ (extensionBarcodeDiagramIso k hp (B i)).symm) ≪≫
      (extensionSectionsIso k hp).app _)

/-- Outside the degrees of a decomposition `K ≅ ⨁_{x ∈ S} (barcodeSheaf k hp (B x))[-x]` the
graded barcode is empty. -/
theorem gradedBarcode_eq_zero_of_iso_biproduct (hp : StrictMono p)
    {K : DerivedCategory (TopCat.Sheaf (ModuleCat.{0} k) realLine)}
    (hK : HasConstructibleCohomology k p K) {S : Finset ℤ}
    {B : ℤ → Multiset (FiniteInterval (2 * m + 1))}
    (e : K ≅ ⨁ fun x : S => (singleFunctor _ x).obj (barcodeSheaf k hp (B x))) {i : ℤ}
    (hi : i ∉ S) : gradedBarcode k hp K hK i = 0 :=
  gradedBarcode_eq_zero_of_isZero k hp hK
    ((isZero_homology_biproduct_single S (fun x => barcodeSheaf k hp (B x)) hi).of_iso
      ((homologyFunctor _ i).mapIso e))

/-- **The graded barcode of a sum of barcode sheaves** placed in the degrees of a finite set `S`
is `B i` in the degrees `i ∈ S` and empty elsewhere. -/
theorem gradedBarcode_biproduct (hp : StrictMono p) (S : Finset ℤ)
    (B : ℤ → Multiset (FiniteInterval (2 * m + 1))) (i : ℤ) :
    gradedBarcode k hp (⨁ fun x : S => (singleFunctor _ x).obj (barcodeSheaf k hp (B x)))
        (hasConstructibleCohomology_biproduct k hp S B) i =
      if i ∈ S then B i else 0 := by
  split_ifs with hi
  · exact gradedBarcode_eq_of_iso_biproduct k hp _ (Iso.refl _) hi
  · exact gradedBarcode_eq_zero_of_iso_biproduct k hp _ (Iso.refl _) hi

end TDA.Sheaf.RealConstructible
