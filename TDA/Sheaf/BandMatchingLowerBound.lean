import TDA.Sheaf.BandIntervalCoefficients
import TDA.Sheaf.BandMatchingProjection
import TDA.Persistence.FiniteMatchingRank
import TDA.Persistence.FiniteOccurrenceMatching

/-!
# Finite graded matching lower bound

Window restrictions transport generators on the original interval sheaves.
The comparison for a two-step convolution uses a source isomorphism
independent of the intermediate label. The projected witness equations give
Hall inequalities on the required occurrences. Common convolution relates
those inequalities to the original graded matching costs.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory Opposite TopologicalSpace
open TDA.Persistence TDA.Persistence.FiniteMatchingRank TDA.Sheaf.AlternatingDiagram
open TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratification
open scoped ENNReal BigOperators

namespace TDA.Sheaf.BandConvolution

section Composition

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {S : C ⥤ D} {L : D ⥤ D} {V W : D ⥤ E} {P Q R : C ⥤ E}

/-- A section comparison from the iterated convolution, using an identification of
the first convolution with a single sheaf. -/
private def iteratedIso
    (eV : S ⋙ L ⋙ V ≅ P) (nW : S ⋙ W ≅ P) (eW : S ⋙ L ⋙ W ≅ R)
    {F F' : C} (a : L.obj (S.obj F) ≅ S.obj F') :
    V.obj (L.obj (L.obj (S.obj F))) ≅ R.obj F :=
  (L ⋙ V).mapIso a ≪≫ eV.app F' ≪≫ (nW.app F').symm ≪≫ (W.mapIso a).symm ≪≫ eW.app F

private theorem section_comp (s : ∀ {A B : C}, Function.Surjective (S.map : (A ⟶ B) → _))
    (eV : S ⋙ L ⋙ V ≅ P) (nW : S ⋙ W ≅ P) (eW : S ⋙ L ⋙ W ≅ R)
    (nV : S ⋙ V ≅ Q) {F F' G K : C} (a : L.obj (S.obj F) ≅ S.obj F')
    (f : L.obj (S.obj F) ⟶ S.obj G) (g : L.obj (S.obj G) ⟶ S.obj K) :
    (iteratedIso eV nW eW a).inv ≫ V.map (L.map f ≫ g) ≫ nV.hom.app K =
      (eW.inv.app F ≫ W.map f ≫ nW.hom.app G) ≫
        (eV.inv.app G ≫ V.map g ≫ nV.hom.app K) := by
  obtain ⟨h, hh⟩ := s (a.inv ≫ f)
  have hf : f = a.hom ≫ S.map h := by rw [hh, a.hom_inv_id_assoc]
  have hn' : W.map (S.map h) ≫ nW.hom.app G = nW.hom.app F' ≫ P.map h :=
    nW.hom.naturality h
  have hmove : eV.inv.app F' ≫ V.map (L.map (S.map h)) = P.map h ≫ eV.inv.app G :=
    (eV.inv.naturality h).symm
  have hcancel : V.map (L.map a.inv) ≫ V.map (L.map a.hom) = 𝟙 _ := by
    rw [← V.map_comp, ← L.map_comp, a.inv_hom_id, L.map_id, V.map_id]
  rw [hf]
  simp only [iteratedIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.comp_map, Iso.app_inv, Iso.app_hom, Functor.map_comp, Category.assoc,
    reassoc_of% hcancel, reassoc_of% hmove, reassoc_of% hn']

end Composition

variable (k : Type) [Field k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))]

local notation "Sh" => realLine.Sheaf (ModuleCat k)
local notation "Single" => Plus.singleFunctor Sh
local notation "H[" d "]" => Plus.homologyFunctor Sh d

private abbrev sections (U : Opens realLine) : Sh ⥤ ModuleCat k where
  obj F := F.presheaf.obj (op U)
  map f := f.hom.app (op U)

private theorem sectionsAdditive (U : Opens realLine) : (sections k U).Additive :=
  { map_add := rfl }

attribute [local instance] sectionsAdditive

private def singleSectionsIso (d : ℤ) (U : Opens realLine) :
    Single d ⋙ (H[d] ⋙ sections k U) ≅ sections k U :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singleFunctorCompHomologyFunctorIsoPlus Sh d) (sections k U) ≪≫
    Functor.leftUnitor _

omit [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))] in
private theorem single_map_surjective (d : ℤ) {F G : Sh} :
    Function.Surjective ((Single d).map : (F ⟶ G) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (DerivedCategory.singleFunctor Sh d).map_surjective (Plus.ι.map f)
  exact ⟨g, Plus.ι.map_injective hg⟩

private def bandSectionsIso (r : ℝ) (d : ℤ) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) :
    Single d ⋙ T k r ⋙ (H[d] ⋙ sections k U) ≅ sections k (bandOpen r U) :=
  (Functor.associator _ _ _).symm ≪≫ bandCohomologySectionsIso k r d U hU

private def bandSectionMap {r : ℝ} {d : ℤ} {F G : Sh}
    (f : (T k r).obj ((Single d).obj F) ⟶ (Single d).obj G)
    (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    (sections k (bandOpen r U)).obj F ⟶ (sections k U).obj G :=
  (bandSectionsIso k r d U hU).inv.app F ≫
    (H[d] ⋙ sections k U).map f ≫ (singleSectionsIso k d U).hom.app G

private abbrev iteratedBandSectionsIso {r : ℝ} {d : ℤ} {F F' : Sh}
    (a : (T k r).obj ((Single d).obj F) ≅ (Single d).obj F')
    (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :=
  iteratedIso (S := Single d) (L := T k r) (V := H[d] ⋙ sections k U)
    (W := H[d] ⋙ sections k (bandOpen r U)) (bandSectionsIso k r d U hU)
    (singleSectionsIso k d (bandOpen r U))
    (bandSectionsIso k r d (bandOpen r U) (ordConnected_bandOpen r hU)) a

private theorem bandSectionMap_comp {r : ℝ} {d : ℤ} {F F' G K : Sh}
    (a : (T k r).obj ((Single d).obj F) ≅ (Single d).obj F')
    (f : (T k r).obj ((Single d).obj F) ⟶ (Single d).obj G)
    (g : (T k r).obj ((Single d).obj G) ⟶ (Single d).obj K)
    (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) :
    (iteratedBandSectionsIso k a U hU).inv ≫
        (H[d] ⋙ sections k U).map ((T k r).map f ≫ g) ≫
        (singleSectionsIso k d U).hom.app K =
      bandSectionMap k f (bandOpen r U) (ordConnected_bandOpen r hU) ≫
        bandSectionMap k g U hU :=
  section_comp (L := T k r) (V := H[d] ⋙ sections k U)
    (W := H[d] ⋙ sections k (bandOpen r U)) (single_map_surjective k d)
    (bandSectionsIso k r d U hU) (singleSectionsIso k d (bandOpen r U))
    (bandSectionsIso k r d (bandOpen r U) (ordConnected_bandOpen r hU))
    (singleSectionsIso k d U) a f g


private theorem bandSectionMap_restrict {r : ℝ} (hr : 0 ≤ r) {d : ℤ} {F G : Sh}
    (f : (T k r).obj ((Single d).obj F) ⟶ (Single d).obj G)
    {V U : Opens realLine} (h : V ≤ U)
    (hV : (V : Set ℝ).OrdConnected) (hU : (U : Set ℝ).OrdConnected) :
    bandSectionMap k f U hU ≫ G.presheaf.map (homOfLE h).op =
      F.presheaf.map (homOfLE (bandOpen_mono_right r h)).op ≫ bandSectionMap k f V hV := by
  let eU := (bandSectionsIso k r d U hU).app F
  let eV := (bandSectionsIso k r d V hV).app F
  let η := (singleFunctorCompHomologyFunctorIsoPlus Sh d).hom.app G
  let u := H[d].map f ≫ η
  have he : ((H[d]).obj ((T k r).obj ((Single d).obj F))).presheaf.map (homOfLE h).op ≫
      eV.hom = eU.hom ≫ F.presheaf.map (homOfLE (bandOpen_mono_right r h)).op :=
    bandCohomologySectionsIso_hom_map (k := k) hr d F h hV hU
  apply (cancel_epi eU.hom).mp
  change _ ≫ (eU.inv ≫ (sections k U).map (H[d].map f) ≫ (sections k U).map η) ≫ _ =
    _ ≫ _ ≫ eV.inv ≫ (sections k V).map (H[d].map f) ≫ (sections k V).map η
  have hright : eU.hom ≫ F.presheaf.map (homOfLE (bandOpen_mono_right r h)).op ≫
      eV.inv ≫ (sections k V).map (H[d].map f) ≫ (sections k V).map η =
        ((H[d]).obj ((T k r).obj ((Single d).obj F))).presheaf.map (homOfLE h).op ≫
          (sections k V).map u := by
    rw [← reassoc_of% he, Iso.hom_inv_id_assoc, ← (sections k V).map_comp]
    rfl
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← (sections k U).map_comp, hright]
  exact (u.hom.naturality (homOfLE h).op).symm

section Interval

variable {k}

/-- A presentation of an interval sheaf and its real support. -/
private structure IntervalModel where
  m : ℕ
  p : Fin m → ℝ
  hp : StrictMono p
  interval : FiniteInterval (2 * m + 1)
  endpoints : IntervalEndpoints
  support_eq : intervalSet p interval = endpoints.support

private abbrev IntervalModel.sheaf (A : IntervalModel) : Sh :=
  (extension k A.hp).obj (AlternatingDiagram.interval (orient A.m) A.interval)

local notation "ISh[" A "]" => IntervalModel.sheaf (k := k) A

omit [HasDerivedCategory Sh] [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))] in
private theorem IntervalModel.finrank_sections (A : IntervalModel) {U : Opens realLine}
    (hU : (U : Set ℝ).OrdConnected) (hwin : U ≤ A.endpoints.openWindow)
    (hne : ((U : Set ℝ) ∩ A.endpoints.support).Nonempty) :
    Module.finrank k ((sections k U).obj ISh[A]) = 1 := by
  apply finrank_sections_extension_interval_eq_one k A.hp A.interval hU
  · rw [A.support_eq]
    exact A.endpoints.closure_inter_openWindow_subset hwin
  · rwa [A.support_eq]

private def IntervalModel.windowGenerator (A : IntervalModel) :
    {s : (sections k A.endpoints.openWindow).obj ISh[A] // s ≠ 0} := by
  have h := A.finrank_sections (k := k) A.endpoints.ordConnected_openWindow le_rfl
    (A.endpoints.support_nonempty.mono fun _ hx => ⟨A.endpoints.mem_openWindow hx, hx⟩)
  let e := ((finrank_eq_one_iff' (K := k) (V := (sections k _).obj ISh[A])).mp h)
  exact ⟨e.choose, e.choose_spec.1⟩

private def IntervalModel.generator (A : IntervalModel) {U : Opens realLine}
    (h : U ≤ A.endpoints.openWindow) : (sections k U).obj ISh[A] :=
  ISh[A].presheaf.map (homOfLE h).op (A.windowGenerator (k := k)).val

omit [HasDerivedCategory Sh] [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))] in
private theorem IntervalModel.map_generator (A : IntervalModel) {V U : Opens realLine}
    (h : V ≤ U) (hU : U ≤ A.endpoints.openWindow) :
    ISh[A].presheaf.map (homOfLE h).op (A.generator (k := k) hU) =
      A.generator (h.trans hU) := by
  have he := ISh[A].presheaf.map_comp (homOfLE hU).op (homOfLE h).op
  exact (ConcreteCategory.congr_hom he A.windowGenerator.val).symm

omit [HasDerivedCategory Sh] [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))] in
private theorem IntervalModel.generator_ne_zero (A : IntervalModel) {U : Opens realLine}
    (hU : (U : Set ℝ).OrdConnected) (hwin : U ≤ A.endpoints.openWindow)
    {x : ℝ} (hx : x ∈ U) (hA : x ∈ A.endpoints.support) :
    A.generator (k := k) hwin ≠ 0 := by
  have hg (V : Opens realLine) (hV : V ≤ A.endpoints.openWindow) :
      closure (intervalSet A.p A.interval) ∩ V ⊆ intervalSet A.p A.interval := by
    rw [A.support_eq]
    exact A.endpoints.closure_inter_openWindow_subset hV
  have hi := isIso_map_extension_interval k A.hp A.interval hwin hU
    A.endpoints.ordConnected_openWindow (hg U hwin) (hg _ le_rfl) hx (A.support_eq ▸ hA)
  exact fun hz => A.windowGenerator.property
    ((asIso (ISh[A].presheaf.map (homOfLE hwin).op)).toLinearEquiv.map_eq_zero_iff.mp hz)

variable [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

private def IntervalModel.convolution {r : ℝ} (hr : 0 ≤ r) (d : ℤ)
    (A : IntervalModel) (hA : A.endpoints.hasDegreeOneOutput = false) :
    Σ B : IntervalModel, (T k r).obj ((Single d).obj ISh[A]) ≅ (Single d).obj ISh[B] := by
  let C := exists_iso_convolved_endpoints k A.hp A.interval d hr A.endpoints hA A.support_eq
  exact ⟨⟨_, _, strictMono_sortedBreakpoints _, C.choose,
    A.endpoints.convolved r hr, C.choose_spec.1⟩,
    C.choose_spec.2.some⟩

private theorem IntervalModel.homologyMap_ne_zero (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    {f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B]} (hf : f ≠ 0) :
    H[d].map f ≠ 0 := by
  let e := (A.convolution (k := k) hr d hA).2
  intro hz
  apply hf
  apply (homology_map_bijective_of_iso_single k e (Iso.refl _)).injective
  rw [Functor.map_zero]
  exact hz

private theorem IntervalModel.allowed (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    {f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B]} (hf : f ≠ 0) :
    (A.endpoints.convolved r hr).homAllowed B.endpoints := by
  let C := (A.convolution (k := k) hr d hA).1
  let e := (A.convolution (k := k) hr d hA).2
  let z := singleFunctorCompHomologyFunctorIsoPlus Sh d
  let a : H[d].obj ((T k r).obj ((Single d).obj ISh[A])) ≅ ISh[C] :=
    H[d].mapIso e ≪≫ z.app ISh[C]
  let b : H[d].obj ((Single d).obj ISh[B]) ≅ ISh[B] := z.app ISh[B]
  by_contra h
  have hz := C.endpoints.hom_eq_zero_of_not_homAllowed k C.hp B.hp B.endpoints
    C.support_eq B.support_eq h (a.inv ≫ H[d].map f ≫ b.hom)
  apply A.homologyMap_ne_zero B hr hA hf
  exact (cancel_epi a.inv).mp ((cancel_mono b.hom).mp (by simpa only
    [Category.assoc, zero_comp, comp_zero] using hz))

private theorem IntervalModel.sectionsMap_ne_zero (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    {f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B]} (hf : f ≠ 0)
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (hwin : U ≤ (A.endpoints.convolved r hr).openWindow) {x : ℝ}
    (hxU : x ∈ U) (hx : x ∈ (A.endpoints.convolved r hr).support ∩ B.endpoints.support) :
    (H[d] ⋙ sections k U).map f ≠ 0 := by
  let C := (A.convolution (k := k) hr d hA).1
  let e := (A.convolution (k := k) hr d hA).2
  let z := singleFunctorCompHomologyFunctorIsoPlus Sh d
  let a : H[d].obj ((T k r).obj ((Single d).obj ISh[A])) ≅ ISh[C] :=
    H[d].mapIso e ≪≫ z.app ISh[C]
  let b : H[d].obj ((Single d).obj ISh[B]) ≅ ISh[B] := z.app ISh[B]
  let u : ISh[C] ⟶ ISh[B] := a.inv ≫ H[d].map f ≫ b.hom
  have hu : u ≠ 0 := fun h => A.homologyMap_ne_zero B hr hA hf
    ((cancel_epi a.inv).mp ((cancel_mono b.hom).mp (by simpa only
      [u, Category.assoc, zero_comp, comp_zero] using h)))
  let stalk := TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) x
  have hst : stalk.map u.hom ≠ 0 := by
    intro hz
    apply hu
    have hi := C.endpoints.bijective_stalkMap_of_homAllowed k C.hp B.hp B.endpoints
      C.support_eq B.support_eq (A.allowed B hr hA hf) hx
    apply hi.injective
    change stalk.map u.hom = stalk.map (0 : ISh[C].presheaf ⟶ ISh[B].presheaf)
    rw [stalk.map_zero]
    exact hz
  have hg := isIso_germ_extension_interval k C.hp C.interval hU (U := U)
    (by rw [C.support_eq]; exact C.endpoints.closure_inter_openWindow_subset hwin)
    hxU (C.support_eq ▸ hx.1)
  intro hfU
  have hz : u.hom.app (op U) = 0 := by
    have h : (sections k U).map (H[d].map f) = 0 := hfU
    change (sections k U).map (a.inv ≫ H[d].map f ≫ b.hom) = 0
    rw [(sections k U).map_comp, (sections k U).map_comp, h, zero_comp, comp_zero]
  apply hst
  apply (cancel_epi (ISh[C].presheaf.germ U x hxU)).mp
  have h := TopCat.Presheaf.stalkFunctor_map_germ U x hxU u.hom
  refine h.trans ?_
  rw [hz, zero_comp]
  exact (comp_zero (f := ISh[C].presheaf.germ U x hxU)).symm

private theorem IntervalEndpoints.input_meets (E : IntervalEndpoints) {r : ℝ} (hr : 0 ≤ r)
    (hE : E.hasDegreeOneOutput = false) {U : Opens realLine}
    {x : ℝ} (hx : x ∈ U) (hxs : x ∈ (E.convolved r hr).support) :
    ((bandOpen r U : Set ℝ) ∩ E.support).Nonempty := by
  suffices ∃ y ∈ E.support, dist y x ≤ r by
    obtain ⟨y, hy, hd⟩ := this
    exact ⟨y, mem_bandOpen.mpr ⟨x, hx, hd⟩, hy⟩
  cases E with
  | icc a b hab =>
    change a - r ≤ x ∧ x ≤ b + r at hxs
    refine ⟨max a (min b x), ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩, ?_⟩
    rw [Real.dist_eq, abs_le]
    constructor
    · have h := le_max_right a (min b x)
      have h' : x - r ≤ max a (min b x) :=
        (le_min (by linarith [hxs.2]) (by linarith)).trans h
      linarith
    · have h : max a (min b x) ≤ x + r := max_le (by linarith [hxs.1])
        (by linarith [min_le_right b x])
      linarith
  | ico a b hab =>
    change a - r ≤ x ∧ x < b - r at hxs
    exact ⟨x + r, ⟨by linarith [hxs.1], by linarith [hxs.2]⟩,
      by rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hr]⟩
  | ioc a b hab =>
    change a + r < x ∧ x ≤ b + r at hxs
    exact ⟨x - r, ⟨by linarith [hxs.1], by linarith [hxs.2]⟩,
      by rw [Real.dist_eq, show x - r - x = -r by ring, abs_neg, abs_of_nonneg hr]⟩
  | ioo => cases hE
  | ici a =>
    change a - r ≤ x at hxs
    refine ⟨max a x, Set.mem_Ici.mpr (le_max_left _ _), ?_⟩
    rw [Real.dist_eq, abs_le]
    have h : max a x ≤ x + r := max_le (by linarith) (by linarith)
    constructor <;> linarith [le_max_right a x]
  | iic b =>
    change x ≤ b + r at hxs
    refine ⟨min b x, Set.mem_Iic.mpr (min_le_left _ _), ?_⟩
    rw [Real.dist_eq, abs_le]
    have h : x - r ≤ min b x := le_min (by linarith) (by linarith)
    constructor <;> linarith [min_le_right b x]
  | ioi a =>
    change a + r < x at hxs
    exact ⟨x - r, show a < x - r by linarith,
      by rw [Real.dist_eq, show x - r - x = -r by ring, abs_neg, abs_of_nonneg hr]⟩
  | iio b =>
    change x < b - r at hxs
    exact ⟨x + r, show x + r < b by linarith,
      by rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hr]⟩
  | univ => exact ⟨x, trivial, by simpa⟩

omit [HasDerivedCategory Sh] [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem eq_zero_of_apply_generator {V W : ModuleCat k} (hV : Module.finrank k V = 1)
    {v : V} (hv : v ≠ 0) (f : V ⟶ W) (h : f v = 0) : f = 0 := by
  apply ModuleCat.hom_ext
  ext w
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hV w
  change f (c • v) = 0
  rw [map_smul, h, smul_zero]

omit [HasDerivedCategory Sh] [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem eval_eq_zero_iff {V V' W W' : ModuleCat k}
    (e : V' ≅ V) (i : W' ≅ W) (u : V' ⟶ W') (v : V)
    (h : Module.finrank k V = 1) (hv : v ≠ 0) :
    (e.inv ≫ u ≫ i.hom) v = 0 ↔ u = 0 := by
  constructor
  · intro hz
    have he := eq_zero_of_apply_generator h hv (e.inv ≫ u ≫ i.hom) hz
    apply (cancel_mono i.hom).mp
    apply (cancel_epi e.inv).mp
    rw [zero_comp, comp_zero]
    exact he
  · rintro rfl
    rw [zero_comp, comp_zero]
    rfl

private theorem IntervalModel.exists_coefficient (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    (f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B]) :
    ∃ c : k, (c = 0 ↔ f = 0) ∧
      ∀ (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected)
        (h₁ : U ≤ (A.endpoints.convolved r hr).openWindow) (h₂ : U ≤ B.endpoints.openWindow),
        bandSectionMap k f U hU
          (A.generator (A.endpoints.bandOpen_openWindow_le hr hA h₁)) = c • B.generator h₂ := by
  by_cases hf : f = 0
  · subst f
    refine ⟨0, by simp, ?_⟩
    intro U hU h₁ h₂
    unfold bandSectionMap
    rw [(H[d] ⋙ sections k U).map_zero, zero_comp, comp_zero, zero_smul]
    rfl
  let E := A.endpoints.convolved r hr
  let U := E.openWindow ⊓ B.endpoints.openWindow
  have hU : (U : Set ℝ).OrdConnected :=
    E.ordConnected_openWindow.inter B.endpoints.ordConnected_openWindow
  have hw : bandOpen r U ≤ A.endpoints.openWindow :=
    A.endpoints.bandOpen_openWindow_le hr hA inf_le_left
  obtain ⟨x, hx⟩ := (A.allowed B hr hA hf).1
  have hxU : x ∈ U := ⟨E.mem_openWindow hx.1, B.endpoints.mem_openWindow hx.2⟩
  have hV := ordConnected_bandOpen r hU
  obtain ⟨y, hy⟩ := A.endpoints.input_meets hr hA hxU hx.1
  have h₁ := A.finrank_sections (k := k) hV hw ⟨y, hy⟩
  have h₂ := B.finrank_sections (k := k) hU inf_le_right ⟨x, hxU, hx.2⟩
  have hy' := A.generator_ne_zero (k := k) hV hw hy.1 hy.2
  have hx' := B.generator_ne_zero (k := k) hU inf_le_right hxU hx.2
  let φ := bandSectionMap k f U hU
  have hφ : φ ≠ 0 := by
    have hne := A.sectionsMap_ne_zero B hr hA hf hU inf_le_left hxU hx
    intro hz
    apply hne
    apply (cancel_epi ((bandSectionsIso k r d U hU).inv.app ISh[A])).mp
    apply (cancel_mono ((singleSectionsIso k d U).hom.app ISh[B])).mp
    change (bandSectionsIso k r d U hU).inv.app ISh[A] ≫
      ((H[d] ⋙ sections k U).map f ≫ (singleSectionsIso k d U).hom.app ISh[B]) =
      (bandSectionsIso k r d U hU).inv.app ISh[A] ≫
        (0 ≫ (singleSectionsIso k d U).hom.app ISh[B])
    rw [zero_comp, comp_zero]
    exact hz
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hx').mp h₂ (φ (A.generator hw))
  refine ⟨c, ⟨fun h => ?_, fun h => (hf h).elim⟩, ?_⟩
  · exact (hφ (eq_zero_of_apply_generator h₁ hy' φ (by rw [← hc, h, zero_smul]))).elim
  · intro V hVc h₁ h₂
    let h : V ≤ U := le_inf h₁ h₂
    have hs := bandSectionMap_restrict k hr f h hVc hU
    have he := ConcreteCategory.congr_hom hs (A.generator hw)
    change ISh[B].presheaf.map (homOfLE h).op (φ (A.generator hw)) =
      bandSectionMap k f V hVc
        (ISh[A].presheaf.map (homOfLE (bandOpen_mono_right r h)).op (A.generator hw)) at he
    rw [← hc, map_smul, B.map_generator, A.map_generator] at he
    exact he.symm

private def IntervalModel.coefficient (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    (f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B]) : k :=
  (A.exists_coefficient B hr hA f).choose

private theorem IntervalModel.coefficient_eq_zero (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    (f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B]) :
    A.coefficient B hr hA f = 0 ↔ f = 0 :=
  (A.exists_coefficient B hr hA f).choose_spec.1

private theorem IntervalModel.bandSectionMap_generator (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    (f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B])
    {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (h₁ : U ≤ (A.endpoints.convolved r hr).openWindow) (h₂ : U ≤ B.endpoints.openWindow) :
    bandSectionMap k f U hU
      (A.generator (A.endpoints.bandOpen_openWindow_le hr hA h₁)) =
      A.coefficient B hr hA f • B.generator h₂ :=
  (A.exists_coefficient B hr hA f).choose_spec.2 U hU h₁ h₂

private theorem IntervalModel.coordinates_le_of_ne_zero (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    (ht : A.endpoints.sameType B.endpoints = true)
    {f : (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B]} (hf : f ≠ 0) :
    A.endpoints.coordinates.1 ≤ B.endpoints.coordinates.1 + r ∧
      A.endpoints.coordinates.2 ≤ B.endpoints.coordinates.2 + r :=
  A.endpoints.coordinates_le_add_of_nonzero_band_hom k A.hp B.hp A.interval B.interval d
    B.endpoints A.support_eq B.support_eq hA ht hr hf

private theorem convolved_stable (E : IntervalEndpoints) {r : ℝ} (hr : 0 ≤ r)
    (hE : E.hasDegreeOneOutput = false) :
    (E.convolved r hr).hasDegreeOneOutput = false := by cases E <;> exact hE

variable [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]

private theorem IntervalModel.iteratedMap_ne_zero (A B : IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false) {d : ℤ}
    {f : (T k r).obj ((T k r).obj ((Single d).obj ISh[A])) ⟶ (Single d).obj ISh[B]}
    (hf : f ≠ 0) {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    (hwin : U ≤ (A.endpoints.convolved (r + r) (add_nonneg hr hr)).openWindow)
    {x : ℝ} (hxU : x ∈ U)
    (hx : x ∈ (A.endpoints.convolved (r + r) (add_nonneg hr hr)).support ∩ B.endpoints.support) :
    (H[d] ⋙ sections k U).map f ≠ 0 := by
  let μ := (TComp k hr hr).app ((Single d).obj ISh[A])
  have hn : μ.inv ≫ f ≠ 0 := by
    intro h
    apply hf
    exact (cancel_epi μ.inv).mp (h.trans (comp_zero (f := μ.inv)).symm)
  have h := A.sectionsMap_ne_zero B (add_nonneg hr hr) hA hn hU hwin hxU hx
  intro hz
  apply h
  rw [Functor.map_comp, hz, comp_zero]

omit [HasDerivedCategory Sh] [∀ r : ℝ, HasDerivedCategory ((D r).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem eval_map_sum {D : Type*} [Category D] [Preadditive D]
    (Q : D ⥤ ModuleCat k) [Q.Additive] {J : Type} [Fintype J] {A B : D}
    {V W : ModuleCat k} (a : V ⟶ Q.obj A) (b : Q.obj B ⟶ W) (c : J → (A ⟶ B))
    (v : V) :
    (a ≫ Q.map (∑ j, c j) ≫ b) v = ∑ j, (a ≫ Q.map (c j) ≫ b) v := by
  rw [Q.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  change (∑ j, a ≫ Q.map (c j) ≫ b).hom v = ∑ j, (a ≫ Q.map (c j) ≫ b).hom v
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]

private theorem IntervalModel.scalar_product_sum_eq_zero_iff
    {J : Type} [Fintype J] (A C : IntervalModel) (B : J → IntervalModel) {r : ℝ}
    (hr : 0 ≤ r) (hA : A.endpoints.hasDegreeOneOutput = false)
    (hB : ∀ j, (B j).endpoints.hasDegreeOneOutput = false)
    (ht : A.endpoints.sameType C.endpoints = true)
    (hl : ∀ j, A.endpoints.sameType (B j).endpoints = true)
    (ht' : ∀ j, (B j).endpoints.sameType C.endpoints = true)
    (hreq : ENNReal.ofReal r < A.endpoints.deletionCost)
    (hreqC : ENNReal.ofReal r < C.endpoints.deletionCost)
    (hscore : C.endpoints.coordinates.1 + C.endpoints.coordinates.2 ≤
      A.endpoints.coordinates.1 + A.endpoints.coordinates.2) (d : ℤ)
    (f : ∀ j, (T k r).obj ((Single d).obj ISh[A]) ⟶ (Single d).obj ISh[B j])
    (g : ∀ j, (T k r).obj ((Single d).obj ISh[B j]) ⟶ (Single d).obj ISh[C]) :
    (∑ j, (B j).coefficient C hr (hB j) (g j) * A.coefficient (B j) hr hA (f j)) = 0 ↔
      (∑ j, H[d].map ((T k r).map (f j) ≫ g j)) = 0 := by
  classical
  let a j := A.coefficient (B j) hr hA (f j)
  let b j := (B j).coefficient C hr (hB j) (g j)
  let c j := (T k r).map (f j) ≫ g j
  change (∑ j, b j * a j) = 0 ↔ (∑ j, H[d].map (c j)) = 0
  -- A nonzero pair of factors supplies the two-step outer coordinate bound.
  by_cases hpath : ∃ j, f j ≠ 0 ∧ g j ≠ 0
  swap
  · push Not at hpath
    have hz (j : J) : b j * a j = 0 ∧ c j = 0 := by
      by_cases hf : f j = 0
      · have ha := (A.coefficient_eq_zero (B j) hr hA (f j)).mpr hf
        simp only [a, c, hf, ha, mul_zero, Functor.map_zero, zero_comp, and_self]
      · have hg := hpath j hf
        have hb := ((B j).coefficient_eq_zero C hr (hB j) (g j)).mpr hg
        simp only [b, c, hg, hb, zero_mul, comp_zero, and_self]
    simp only [fun j => (hz j).1, fun j => (hz j).2, Functor.map_zero, Finset.sum_const_zero]
  obtain ⟨j, hf, hg⟩ := hpath
  obtain ⟨h₁, h₂⟩ := A.coordinates_le_of_ne_zero (B j) hr hA (hl j) hf
  obtain ⟨h₃, h₄⟩ := (B j).coordinates_le_of_ne_zero C hr (hB j) (ht' j) hg
  obtain ⟨x, hx⟩ := A.endpoints.outer_overlap_of_score_le C.endpoints hr hA ht hreq hreqC hscore
    (by linarith) (by linarith)
  let E := A.endpoints.convolved (r + r) (add_nonneg hr hr)
  let U := E.openWindow ⊓ C.endpoints.openWindow
  let V := bandOpen r U
  have hU : (U : Set ℝ).OrdConnected :=
    E.ordConnected_openWindow.inter C.endpoints.ordConnected_openWindow
  have hV := ordConnected_bandOpen r hU
  have hxU : x ∈ U := ⟨E.mem_openWindow hx.1, C.endpoints.mem_openWindow hx.2⟩
  let A' := (A.convolution (k := k) hr d hA).1
  let e := (A.convolution (k := k) hr d hA).2
  have hA' : A'.endpoints.hasDegreeOneOutput = false := convolved_stable _ hr hA
  have hE : A'.endpoints.convolved r hr = E := A.endpoints.convolved_add hr hr
  have hwin : U ≤ (A'.endpoints.convolved r hr).openWindow := hE ▸ inf_le_left
  have hwV : V ≤ A'.endpoints.openWindow := A'.endpoints.bandOpen_openWindow_le hr hA' hwin
  have hw : bandOpen r V ≤ A.endpoints.openWindow :=
    A.endpoints.bandOpen_openWindow_le hr hA hwV
  obtain ⟨y, hy⟩ := A'.endpoints.input_meets hr hA' hxU (hE ▸ hx.1)
  obtain ⟨z, hz⟩ := A.endpoints.input_meets hr hA hy.1 hy.2
  let v := A.generator (k := k) hw
  let w := C.generator (k := k) (U := U) inf_le_right
  have hv := A.generator_ne_zero (k := k) (ordConnected_bandOpen r hV) hw hz.1 hz.2
  have hvdim := A.finrank_sections (k := k) (ordConnected_bandOpen r hV) hw ⟨z, hz⟩
  have hwne := C.generator_ne_zero (k := k) hU inf_le_right hxU hx.2
  let Q := H[d] ⋙ sections k U
  let η := (singleSectionsIso k d U).app ISh[C]
  let iso := iteratedBandSectionsIso k e U hU
  let read (m : _ ⟶ _) := iso.inv ≫ Q.map m ≫ η.hom
  have hread (j : J) : read (c j) v = (b j * a j) • w := by
    by_cases hf : f j = 0
    · have ha := (A.coefficient_eq_zero (B j) hr hA (f j)).mpr hf
      simp only [a, c, read, hf, ha, mul_zero, zero_smul, (T k r).map_zero, Q.map_zero,
        zero_comp, comp_zero]
      rfl
    by_cases hg : g j = 0
    · have hb := ((B j).coefficient_eq_zero C hr (hB j) (g j)).mpr hg
      simp only [b, c, read, hg, hb, zero_mul, zero_smul, Q.map_zero, zero_comp, comp_zero]
      rfl
    have hmid : U ≤ ((B j).endpoints.convolved r hr).openWindow :=
      hwin.trans (A'.endpoints.convolved_openWindow_le_of_homAllowed (B j).endpoints
        (A.allowed (B j) hr hA hf) hA' (hB j) hr)
    have hmidV := (B j).endpoints.bandOpen_openWindow_le hr (hB j) hmid
    have h := ConcreteCategory.congr_hom (bandSectionMap_comp k e (f j) (g j) U hU) v
    change read (c j) v =
      bandSectionMap k (g j) U hU (bandSectionMap k (f j) V hV v) at h
    rw [h]
    have ha := A.bandSectionMap_generator (B j) hr hA (f j) hV hwV hmidV
    have hb := (B j).bandSectionMap_generator C hr (hB j) (g j) hU hmid inf_le_right
    change bandSectionMap k (f j) V hV v = a j • (B j).generator hmidV at ha
    change bandSectionMap k (g j) U hU ((B j).generator hmidV) = b j • w at hb
    rw [ha, map_smul, hb, smul_smul, mul_comm]
  have hsum : read (∑ j, c j) v = (∑ j, b j * a j) • w := by
    calc
      _ = ∑ j, read (c j) v := eval_map_sum Q iso.inv η.hom c v
      _ = ∑ j, (b j * a j) • w := Finset.sum_congr rfl fun j _ => hread j
      _ = _ := Finset.sum_smul.symm
  let m := ∑ j, c j
  have hread' : read m v = 0 ↔ Q.map m = 0 :=
    eval_eq_zero_iff iso η (Q.map m) v hvdim hv
  have hcoh : Q.map m = 0 ↔ H[d].map m = 0 := by
    constructor
    · intro hmap
      by_contra hm
      have hn : m ≠ 0 := fun h => hm (h.symm ▸ H[d].map_zero _ _)
      exact A.iteratedMap_ne_zero C hr hA hn hU inf_le_left hxU hx hmap
    · intro h
      change (sections k U).map (H[d].map m) = 0
      rw [h, (sections k U).map_zero]
  have hs : (∑ j, b j * a j) = 0 ↔ read m v = 0 := by
    rw [hsum]
    exact ⟨fun h => h.symm ▸ zero_smul k w,
      fun h => (smul_eq_zero.mp h).resolve_right hwne⟩
  have hH : H[d].map m = ∑ j, H[d].map (c j) := H[d].map_sum _ _
  exact hs.trans (hread'.trans (hcoh.trans (Iff.of_eq (congrArg (· = 0) hH))))

end Interval

section Hall

variable {k}
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

local notation "ISh[" A "]" => IntervalModel.sheaf (k := k) A

private theorem sameType_iff (E F : IntervalEndpoints) :
    E.sameType F = true ↔ E.ctorIdx = F.ctorIdx := by
  cases E <;> cases F <;> constructor <;> intro h <;> first | rfl | cases h

private def degreeIso {d e : ℤ} (h : d = e) (F : Sh) :
    (Single d).obj F ≅ (Single e).obj F :=
  (eqToIso (congrArg (fun n => Single n) h)).app F

private def alignHom {r : ℝ} {d e d' e' : ℤ} {A B : Sh}
    (hd : d = d') (he : e = e')
    (f : (T k r).obj ((Single d).obj A) ⟶ (Single e).obj B) :
    (T k r).obj ((Single d').obj A) ⟶ (Single e').obj B :=
  (T k r).map (degreeIso hd A).inv ≫ f ≫ (degreeIso he B).hom

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem alignHom_rfl {r : ℝ} {d e : ℤ} {A B : Sh}
    (f : (T k r).obj ((Single d).obj A) ⟶ (Single e).obj B) :
    alignHom rfl rfl f = f := by
  simp [alignHom, degreeIso]

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem alignHom_comp {r : ℝ} {d e t : ℤ} {A B C : Sh} (h : e = d) (h' : t = d)
    (f : (T k r).obj ((Single d).obj A) ⟶ (Single e).obj B)
    (g : (T k r).obj ((Single e).obj B) ⟶ (Single t).obj C) :
    H[d].map ((T k r).map (alignHom rfl h f) ≫ alignHom h h' g) =
      H[d].map ((T k r).map f ≫ g) ≫ H[d].map (degreeIso h' C).hom := by
  subst e t
  simp [alignHom_rfl, degreeIso]

omit [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))] in
private theorem IntervalModel.coefficient_align {r : ℝ} (hr : 0 ≤ r) (B C : IntervalModel)
    (hs : B.endpoints.hasDegreeOneOutput = false)
    {d e t : ℤ} (h : e = d) (h' : t = d)
    (g : (T k r).obj ((Single e).obj ISh[B]) ⟶ (Single t).obj ISh[C]) :
    B.coefficient C hr hs (alignHom h h' g) =
      B.coefficient C hr hs (alignHom rfl (h'.trans h.symm) g) := by
  subst e t
  rfl

variable {I J : Type} [Fintype I] [Fintype J]
  {mi : I → ℕ} {nj : J → ℕ} {pi : (i : I) → Fin (mi i) → ℝ} {qj : (j : J) → Fin (nj j) → ℝ}
  (hpi : ∀ i, StrictMono (pi i)) (hqj : ∀ j, StrictMono (qj j))
  {X : (i : I) → GradedInterval (mi i)} {Y : (j : J) → GradedInterval (nj j)}

local notation "XX" => (fun i => GradedInterval.obj k (hpi i) (X i))
local notation "YY" => (fun j => GradedInterval.obj k (hqj j) (Y j))

/-- Every subset of the required stable occurrences has at least as many neighbours
in the same-degree, same-type graph with the radius bound on the signed coordinates. -/
theorem Witness.card_le_neighbors_of_stable (E : I → IntervalEndpoints)
    (F : J → IntervalEndpoints)
    (hX : ∀ i, intervalSet (pi i) (X i).interval = (E i).support)
    (hY : ∀ j, intervalSet (qj j) (Y j).interval = (F j).support)
    (hE : ∀ i, (E i).hasDegreeOneOutput = false)
    (hF : ∀ j, (F j).hasDegreeOneOutput = false) {r : ℝ} (hr : 0 ≤ r)
    (w : Witness k hr (⨁ XX) (⨁ YY)) (S : Finset I)
    (hS : ∀ i ∈ S, ENNReal.ofReal r < (E i).deletionCost) :
    S.card ≤ (FiniteOccurrenceMatching.neighbors (fun i j =>
      (X i).degree = (Y j).degree ∧ (E i).sameType (F j) = true ∧
        max |(E i).coordinates.1 - (F j).coordinates.1|
          |(E i).coordinates.2 - (F j).coordinates.2| ≤ r) S).card := by
  classical
  let L (i : I) : IntervalModel := ⟨_, _, hpi i, (X i).interval, E i, hX i⟩
  let M (j : J) : IntervalModel := ⟨_, _, hqj j, (Y j).interval, F j, hY j⟩
  -- Products between distinct degree and endpoint blocks vanish entrywise.
  let p (i : I) := ((X i).degree, (E i).ctorIdx)
  let q (j : J) := ((Y j).degree, (F j).ctorIdx)
  let score (i : S) := (E i).coordinates.1 + (E i).coordinates.2
  let N := FiniteOccurrenceMatching.neighbors (fun i j =>
    (X i).degree = (Y j).degree ∧ (E i).sameType (F j) = true ∧
      max |(E i).coordinates.1 - (F j).coordinates.1|
        |(E i).coordinates.2 - (F j).coordinates.2| ≤ r) S
  let f (i : I) (j : J) :
      (T k r).obj ((Single (X i).degree).obj ISh[L i]) ⟶
        (Single (Y j).degree).obj ISh[M j] := w.biproductHom XX YY i j
  let g (j : J) (i : I) :
      (T k r).obj ((Single (Y j).degree).obj ISh[M j]) ⟶
        (Single (X i).degree).obj ISh[L i] := w.symm.biproductHom YY XX j i
  let A : Matrix J S k := fun j i =>
    if h : q j = p i then
      (L i).coefficient (M j) hr (hE i) (alignHom rfl (congrArg Prod.fst h) (f i j))
    else 0
  let B : Matrix S J k := fun i j =>
    if h : q j = p i then
      (M j).coefficient (L i) hr (hF j) (alignHom rfl (congrArg Prod.fst h.symm) (g j i))
    else 0
  have hf (i : S) (j : J) (hn : A j i ≠ 0) :
      q j = p i ∧ (E i).coordinates.1 ≤ (F j).coordinates.1 + r ∧
        (E i).coordinates.2 ≤ (F j).coordinates.2 + r := by
    by_cases h : q j = p i
    · rw [show A j i = _ from dite_eq_left h] at hn
      exact ⟨h, (L i).coordinates_le_of_ne_zero (M j) hr (hE i)
        ((sameType_iff _ _).mpr (congrArg Prod.snd h.symm))
        (mt ((L i).coefficient_eq_zero (M j) hr (hE i) _).mpr hn)⟩
    · exact (hn (dite_eq_right h)).elim
  have hg (i : S) (j : J) (hn : B i j ≠ 0) :
      q j = p i ∧ (F j).coordinates.1 ≤ (E i).coordinates.1 + r ∧
        (F j).coordinates.2 ≤ (E i).coordinates.2 + r := by
    by_cases h : q j = p i
    · rw [show B i j = _ from dite_eq_left h] at hn
      exact ⟨h, (M j).coordinates_le_of_ne_zero (L i) hr (hF j)
        ((sameType_iff _ _).mpr (congrArg Prod.snd h))
        (mt ((M j).coefficient_eq_zero (L i) hr (hF j) _).mpr hn)⟩
    · exact (hn (dite_eq_right h)).elim
  have hentry (a i : S) (h : p a = p i) (hs : score a ≤ score i) :
      (B * A) a i = 0 ↔
        H[(X i).degree].map ((TComp k hr hr).hom.app (XX i) ≫
          (aug k (add_nonneg hr hr)).app (XX i) ≫ biproduct.ι XX i ≫ biproduct.π XX a) = 0 := by
    let Z := Finset.univ.filter fun j : J =>
      (Y j).degree = (X i).degree ∧ (E i).sameType (F j) = true
    have hj (j : J) : j ∈ Z ↔ q j = p i := by
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and, sameType_iff, p, q,
        Prod.mk.injEq, eq_comm (a := (E i).ctorIdx)]
    let di := (X i).degree
    let hda : (X a).degree = di := congrArg Prod.fst h
    let jt (j : Z) : (Y j).degree = di := congrArg Prod.fst ((hj j).mp j.property)
    let f' (j : Z) := alignHom rfl (jt j) (f i j)
    let g' (j : Z) := alignHom (jt j) hda (g j a)
    have ha : (E i).sameType (E a) = true :=
      (sameType_iff _ _).mpr (congrArg Prod.snd h.symm)
    have hs₁ (j : Z) : (E i).sameType (F j) = true :=
      (sameType_iff _ _).mpr (congrArg Prod.snd ((hj j).mp j.property).symm)
    have hs₂ (j : Z) : (F j).sameType (E a) = true :=
      (sameType_iff _ _).mpr (congrArg Prod.snd (((hj j).mp j.property).trans h.symm))
    have hm : (B * A) a i =
        ∑ j : Z, (M j).coefficient (L a) hr (hF j) (g' j) *
          (L i).coefficient (M j) hr (hE i) (f' j) := by
      rw [Matrix.mul_apply, ← Finset.sum_subset (Finset.subset_univ Z)
        (fun j _ hj' => mul_eq_zero.mpr (Or.inr (dite_eq_right (mt (hj j).mpr hj')))),
        ← Finset.sum_attach Z]
      refine Finset.sum_congr rfl fun j _ => ?_
      have he := (hj j).mp j.property
      have he' : q j = p a := he.trans h.symm
      change (if h' : q j = p a then (M j).coefficient (L a) hr (hF j)
          (alignHom rfl (congrArg Prod.fst h'.symm) (g j a)) else 0) *
        (if h' : q j = p i then (L i).coefficient (M j) hr (hE i)
          (alignHom rfl (congrArg Prod.fst h') (f i j)) else 0) = _
      rw [dite_eq_left he', dite_eq_left he,
        (M j).coefficient_align hr (L a) (hF j) (jt j) hda (g j a)]
    have hs0 := (L i).scalar_product_sum_eq_zero_iff (L a) (fun j : Z => M j)
      hr (hE i) (fun j => hF j) ha hs₁ hs₂ (hS i i.property) (hS a a.property) hs di f' g'
    let η := H[di].map (degreeIso hda ISh[L a]).hom
    let src := (T k r).obj ((T k r).obj (XX i))
    let u : H[di].obj src ⟶ H[di].obj (XX a) :=
      H[di].map ((TComp k hr hr).hom.app (XX i) ≫
        (aug k (add_nonneg hr hr)).app (XX i) ≫ biproduct.ι XX i ≫ biproduct.π XX a)
    have hsum : (∑ j : Z, H[di].map ((T k r).map (f' j) ≫ g' j)) =
        (∑ j ∈ Z, H[di].map ((T k r).map (f i j) ≫ g j a)) ≫ η := by
      rw [Preadditive.sum_comp, ← Finset.sum_attach Z]
      exact Finset.sum_congr rfl fun j _ => alignHom_comp (jt j) hda (f i j) (g j a)
    have hproj : (∑ j ∈ Z, H[di].map ((T k r).map (f i j) ≫ g j a)) = u :=
      w.sum_homology_biproductHom_in_block hpi hqj hr E F hX hY hE hF i a hda ha
    have htotal := hsum.trans (congrArg (· ≫ η) hproj)
    have hmono : u ≫ η = 0 ↔ u = 0 := by
      constructor
      · intro hz
        exact (cancel_mono η).mp (hz.trans (zero_comp (f := η)).symm)
      · intro hz
        exact hz.symm ▸ zero_comp (f := η)
    exact (Iff.of_eq (congrArg (· = 0) hm)).trans
      (hs0.trans ((Iff.of_eq (congrArg (· = 0) htotal)).trans hmono))
  have hzero (a i : S) (hne : a ≠ i) (hs : score a ≤ score i) : (B * A) a i = 0 := by
    by_cases h : p a = p i
    · apply (hentry a i h hs).mpr
      have hi : (i : I) ≠ (a : I) := fun he => hne (Subtype.ext he.symm)
      simp only [biproduct.ι_π_ne _ hi, comp_zero, Functor.map_zero]
    · rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro j _
      by_contra hj
      exact h ((hg a j (left_ne_zero_of_mul hj)).1.symm.trans
        (hf i j (right_ne_zero_of_mul hj)).1)
  have hdiag (i : S) : (B * A) i i ≠ 0 := by
    intro hz
    have he := (hentry i i rfl le_rfl).mp hz
    have hn := homology_band_augmentation_ne_zero_of_lt_deletionCost (k := k)
      (hpi i) (X i) (E i) (hX i) (hE i) hr (hS i i.property)
    rw [biproduct.ι_π_self] at he
    let t : (T k (r + r)).obj (XX i) ⟶ XX i := (aug k (add_nonneg hr hr)).app (XX i)
    change H[(X i).degree].map ((TComp k hr hr).hom.app (XX i) ≫ t ≫ 𝟙 (XX i)) = 0 at he
    rw [Category.comp_id t] at he
    exact hn he
  have hdiscard (a i : S) (j : J) (hj : j ∉ N) (hn : B a j * A j i ≠ 0) :
      score i < score a := by
    obtain ⟨h₁, hf'⟩ := hf i j (right_ne_zero_of_mul hn)
    obtain ⟨h₂, hg'⟩ := hg a j (left_ne_zero_of_mul hn)
    have hi : r < max |(E i).coordinates.1 - (F j).coordinates.1|
        |(E i).coordinates.2 - (F j).coordinates.2| := by
      apply lt_of_not_ge
      intro h
      exact hj (FiniteOccurrenceMatching.mem_neighbors.mpr ⟨i, i.property,
        congrArg Prod.fst h₁.symm, (sameType_iff _ _).mpr (congrArg Prod.snd h₁.symm), h⟩)
    have ha : r < max |(F j).coordinates.1 - (E a).coordinates.1|
        |(F j).coordinates.2 - (E a).coordinates.2| := by
      apply lt_of_not_ge
      intro h
      exact hj (FiniteOccurrenceMatching.mem_neighbors.mpr ⟨a, a.property,
        congrArg Prod.fst h₂.symm, (sameType_iff _ _).mpr (congrArg Prod.snd h₂.symm),
        by simpa only [abs_sub_comm] using h⟩)
    exact sum_lt_of_sup_abs_sub_gt hf' hg' hi ha
  change S.card ≤ N.card
  simpa only [Fintype.card_coe] using
    card_le_of_restricted_triangular_product A B N score hzero hdiag hdiscard

/-- A finite interleaving of graded interval sums gives a partial matching of
cost at most the radius of the interleaving. -/
theorem Witness.exists_gradedMatching_cost_le {r : ℝ} (hr : 0 ≤ r)
    (w : Witness k hr (⨁ XX) (⨁ YY)) :
    ∃ M : GradedMatching I J, M.cost XX YY ≤ ENNReal.ofReal r := by
  classical
  let E i := IntervalEndpoints.ofInterval (hpi i) (X i).interval
  let F j := IntervalEndpoints.ofInterval (hqj j) (Y j).interval
  have hE i : intervalSet (pi i) (X i).interval = (E i).support :=
    IntervalEndpoints.support_ofInterval (hpi i) (X i).interval
  have hF j : intervalSet (qj j) (Y j).interval = (F j).support :=
    IntervalEndpoints.support_ofInterval (hqj j) (Y j).interval
  obtain ⟨s, hs, hEs, hFs⟩ := exists_normalizing_radius E F
  let P i := (E i).normalized hs.le (hEs i)
  let Q j := (F j).normalized hs.le (hFs j)
  obtain ⟨X', Y', hX', hY', ⟨w'⟩⟩ := w.exists_normalized_biproduct
    hpi hqj E F hE hF hs.le hEs hFs
  let hp' i := strictMono_sortedBreakpoints (bandBreakpoints (pi i) s)
  let hq' j := strictMono_sortedBreakpoints (bandBreakpoints (qj j) s)
  have hP i := (E i).normalized_hasDegreeOneOutput hs.le (hEs i)
  have hQ j := (F j).normalized_hasDegreeOneOutput hs.le (hFs j)
  have hPd i : (P i).deletionCost = (E i).deletionCost :=
    (E i).normalized_deletionCost hs.le (hEs i)
  have hQd j : (Q j).deletionCost = (F j).deletionCost :=
    (F j).normalized_deletionCost hs.le (hFs j)
  let edge i j := (X' i).degree = (Y' j).degree ∧ (P i).sameType (Q j) = true ∧
    max |(P i).coordinates.1 - (Q j).coordinates.1|
      |(P i).coordinates.2 - (Q j).coordinates.2| ≤ r
  let edge' j i := (Y' j).degree = (X' i).degree ∧ (Q j).sameType (P i) = true ∧
    max |(Q j).coordinates.1 - (P i).coordinates.1|
      |(Q j).coordinates.2 - (P i).coordinates.2| ≤ r
  have hsymm : edge' = fun j i => edge i j := by
    funext j i
    apply propext
    simp only [edge, edge', sameType_iff, eq_comm (a := (Y' j).degree),
      eq_comm (a := (Q j).ctorIdx), abs_sub_comm (a := (Q j).coordinates.1),
      abs_sub_comm (a := (Q j).coordinates.2)]
  let L := Finset.univ.filter fun i => ENNReal.ofReal r < (E i).deletionCost
  let N := Finset.univ.filter fun j => ENNReal.ofReal r < (F j).deletionCost
  have hL : ∀ S : Finset I, S ⊆ L → S.card ≤ (FiniteOccurrenceMatching.neighbors edge S).card := by
    intro S hS
    exact w'.card_le_neighbors_of_stable hp' hq' P Q (fun i => (hX' i).1) (fun j => (hY' j).1)
      hP hQ hr S (fun i hi => (hPd i).symm ▸ (Finset.mem_filter.mp (hS hi)).2)
  have hN : ∀ S : Finset J, S ⊆ N → S.card ≤ (FiniteOccurrenceMatching.neighbors edge' S).card := by
    intro S hS
    exact w'.symm.card_le_neighbors_of_stable hq' hp' Q P (fun j => (hY' j).1) (fun i => (hX' i).1)
      hQ hP hr S (fun j hj => (hQd j).symm ▸ (Finset.mem_filter.mp (hS hj)).2)
  rw [hsymm] at hN
  obtain ⟨M, hM, hML, hMN⟩ := FiniteOccurrenceMatching.exists_two_sided_of_hall edge L N hL hN
  refine ⟨M, (GradedMatching.cost_le_iff M).mpr ⟨?_, ?_, ?_⟩⟩
  · intro i j hij
    rw [(E i).distance_eq_totalPairCost k (hpi i) (hqj j) (X i) (Y j) (F j) (hE i) (hF j)]
    apply ((E i).totalPairCost_le_iff_normalizedEdge_or_deletable (F j) (X i).degree (Y j).degree
      hs.le (hEs i) (hFs j) hr).mpr
    refine Or.inl ?_
    simpa only [edge, IntervalEndpoints.normalizedEdge, (hX' i).2.1, (hY' j).2.1] using hM i j hij
  · intro i hi
    rw [(E i).distance_zero_eq k (hpi i) (X i) (hE i)]
    by_contra! hh
    obtain ⟨j, hj⟩ := hML i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    rw [hi] at hj
    cases hj
  · intro j hj
    rw [(F j).distance_zero_eq k (hqj j) (Y j) (hF j)]
    by_contra! hh
    exact hj (hMN j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩))

/-- The least graded matching cost is a lower bound for the distance of the
finite interval sums. -/
theorem matchingDistance_le_distance_biproduct :
    matchingDistance XX YY ≤ distance (⨁ XX) (⨁ YY) := by
  apply le_distance_iff.mpr
  rintro r ⟨w⟩
  obtain ⟨M, hM⟩ := w.exists_gradedMatching_cost_le hpi hqj r.coe_nonneg
  exact (matchingDistance_le_cost M).trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hM)

/-- The distance of finite graded interval sums equals their least matching cost. -/
theorem distance_biproduct_eq_matchingDistance :
    distance (⨁ XX) (⨁ YY) = matchingDistance XX YY :=
  le_antisymm (distance_le_matchingDistance (Iso.refl _) (Iso.refl _))
    (matchingDistance_le_distance_biproduct hpi hqj)

/-- The distance of objects presented as finite graded interval sums equals
the least matching cost of their occurrence families. -/
theorem distance_eq_matchingDistance_of_iso {K L : Plus Sh}
    (e : K ≅ ⨁ XX) (f : L ≅ ⨁ YY) : distance K L = matchingDistance XX YY :=
  (distance_congr e f).trans (distance_biproduct_eq_matchingDistance hpi hqj)

end Hall

section Bounded

variable {k}
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]
  {m n : ℕ} {p : Fin m → ℝ} {q : Fin n → ℝ}

/-- For bounded objects with constructible cohomology, band distance is the
least matching cost of the two graded barcode occurrence families. -/
theorem distanceB_eq_gradedBarcodeMatchingDistance (hp : StrictMono p) (hq : StrictMono q)
    (K L : Bounded Sh) (a b c d : ℤ) [K.obj.IsGE a] [K.obj.IsLE b] [L.obj.IsGE c] [L.obj.IsLE d]
    (hK : HasConstructibleCohomology k p K.obj) (hL : HasConstructibleCohomology k q L.obj) :
    distanceB K L = matchingDistance
      (fun i =>
        (gradedBarcodeOccurrence (Finset.Icc a b) (gradedBarcode k hp K.obj hK) i).obj k hp)
      (fun j =>
        (gradedBarcodeOccurrence (Finset.Icc c d) (gradedBarcode k hq L.obj hL) j).obj k hq) := by
  obtain ⟨e⟩ := nonempty_iso_biproduct_gradedBarcode k hp K a b hK
  obtain ⟨f⟩ := nonempty_iso_biproduct_gradedBarcode k hq L c d hL
  exact distance_eq_matchingDistance_of_iso (fun _ => hp) (fun _ => hq)
    ((boundedToPlus Sh).mapIso e ≪≫ (boundedToPlus Sh).mapBiproduct _)
    ((boundedToPlus Sh).mapIso f ≪≫ (boundedToPlus Sh).mapBiproduct _)

end Bounded

end TDA.Sheaf.BandConvolution
