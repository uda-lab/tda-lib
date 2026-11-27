import TDA.Sheaf.BandIntervalDegreeZero

/-!
# Sections and stalks of band cohomology in a single degree

The same-degree cohomology of band convolution has a natural section comparison on
order-connected opens. It reads coefficients on global sections or, where the
section-to-stalk maps are invertible, on the corresponding stalks.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory DerivedCategory Opposite TopologicalSpace

namespace TDA.Sheaf.BandConvolution

variable (k : Type) [Field k]
  [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

local notation "Sh" => realLine.Sheaf (ModuleCat k)
local notation "D⁺" => Plus Sh
local notation "Single" => Plus.singleFunctor Sh
local notation "H[" d "]" => Plus.homologyFunctor Sh d
local notation "Coh[" r "," d "]" => Single d ⋙ T k r ⋙ H[d]
local notation "Sect[" U "]" =>
  TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    Functor.obj (evaluation (Opens realLine)ᵒᵖ (ModuleCat k)) (op U)

private def bandCohomologyShiftIso (r : ℝ) (d : ℤ) : Coh[r,d] ≅ Coh[r,0] := by
  by_cases hd : d = 0
  · subst d
    exact Iso.refl _
  · let S := shiftFunctor D⁺ (-d)
    let eS : Single d ≅ Single 0 ⋙ S :=
      ((Plus.singleFunctors Sh).shiftIso (-d) d 0 (by omega)).symm
    let eH : S ⋙ H[d] ≅ H[0] := H[0].shiftIso (-d) d 0 (by omega)
    exact Functor.isoWhiskerRight eS (T k r ⋙ H[d]) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Single 0)
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight ((T k r).commShiftIso (-d)) (H[d]) ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (T k r) eH)

/-- In the degree of a single sheaf, sections after convolution are naturally
identified with sections on the thickened open. The degree-zero comparison is
obtained from `H0TIso` and the natural thickening formula. -/
def bandCohomologySectionsIso (r : ℝ) (d : ℤ) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) :
    Coh[r,d] ⋙ Sect[U] ≅ Sect[bandOpen r U] :=
  Functor.isoWhiskerRight (bandCohomologyShiftIso k r d) _ ≪≫
    Functor.isoWhiskerRight (H0TIso k r) _ ≪≫ thickeningSectionsNatIso k r U hU

/-- In degree zero the section comparison is `H0TSectionsIso`. -/
theorem bandCohomologySectionsIso_app_zero (r : ℝ) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) (F : Sh) :
    (bandCohomologySectionsIso k r 0 U hU).app F = H0TSectionsIso k r F U hU := by
  apply Iso.ext
  simp [bandCohomologySectionsIso, bandCohomologyShiftIso, H0TSectionsIso,
    Functor.isoWhiskerRight, thickeningSectionsNatIso]
  rfl

/-- At nonnegative radius, same-degree convolution cohomology acts on global sections
by the original map under the natural section identifications. -/
def bandCohomologyGlobalSectionsIso {r : ℝ} (hr : 0 ≤ r) (d : ℤ) :
    Coh[r,d] ⋙ Sect[⊤] ≅ Sect[⊤] :=
  bandCohomologySectionsIso k r d ⊤ Set.ordConnected_univ ≪≫
    eqToIso (congrArg (fun U : Opens realLine => Sect[U]) (top_unique (le_bandOpen hr ⊤)))

variable {k}

/-- Stalk comparison through an order-connected open and its thickening when both
germs are isomorphisms. The comparison identifies the generators transported
from sections of the thickened open. -/
def bandCohomologyStalkIso (r : ℝ) (d : ℤ) (F : Sh) (U : Opens realLine)
    (hU : (U : Set ℝ).OrdConnected) {x y : ℝ} (hx : x ∈ U) (hy : y ∈ bandOpen r U)
    [out : IsIso (((Coh[r,d]).obj F).presheaf.germ U x hx)]
    [input : IsIso (F.presheaf.germ (bandOpen r U) y hy)] :
    ((Coh[r,d]).obj F).presheaf.stalk x ≅ F.presheaf.stalk y := by
  let eOut := @asIso _ _ _ _ _ out
  let eIn := @asIso _ _ _ _ _ input
  exact eOut.symm ≪≫ (bandCohomologySectionsIso k r d U hU).app F ≪≫ eIn

/-- A morphism on the convolution stalk has the original coefficient in bases
transported through the section comparisons on a common open. -/
theorem bandCohomologyStalkIso_hom_naturality (r : ℝ) (d : ℤ) {F G : Sh} (f : F ⟶ G)
    (U : Opens realLine) (hU : (U : Set ℝ).OrdConnected) {x y : ℝ}
    (hx : x ∈ U) (hy : y ∈ bandOpen r U)
    [outF : IsIso (((Coh[r,d]).obj F).presheaf.germ U x hx)]
    [outG : IsIso (((Coh[r,d]).obj G).presheaf.germ U x hx)]
    [IsIso (F.presheaf.germ (bandOpen r U) y hy)]
    [IsIso (G.presheaf.germ (bandOpen r U) y hy)] :
    (TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) x).map
        ((Coh[r,d]).map f).hom ≫ (bandCohomologyStalkIso r d G U hU hx hy).hom =
      (bandCohomologyStalkIso r d F U hU hx hy).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) y).map f.hom := by
  let e := bandCohomologySectionsIso k r d U hU
  let gF := ((Coh[r,d]).obj F).presheaf.germ U x hx
  let gG := ((Coh[r,d]).obj G).presheaf.germ U x hx
  let iF := @asIso _ _ _ _ gF outF
  let iG := @asIso _ _ _ _ gG outG
  let tF := F.presheaf.germ (bandOpen r U) y hy
  let tG := G.presheaf.germ (bandOpen r U) y hy
  let st (z : ℝ) := TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) z
  let tf := (Coh[r,d]).map f
  have hn := e.hom.naturality f
  change tf.hom.app (op U) ≫ e.hom.app G =
    e.hom.app F ≫ f.hom.app (op (bandOpen r U)) at hn
  have hg : gF ≫ (st x).map tf.hom = tf.hom.app (op U) ≫ gG :=
    TopCat.Presheaf.stalkFunctor_map_germ U x hx tf.hom
  have ht : tF ≫ (st y).map f.hom = f.hom.app (op (bandOpen r U)) ≫ tG :=
    TopCat.Presheaf.stalkFunctor_map_germ (bandOpen r U) y hy f.hom
  change (st x).map tf.hom ≫ iG.inv ≫ e.hom.app G ≫ tG =
    (iF.inv ≫ e.hom.app F ≫ tF) ≫ (st y).map f.hom
  apply (cancel_epi iF.hom).mp
  change gF ≫ (st x).map tf.hom ≫ iG.inv ≫ e.hom.app G ≫ tG =
    iF.hom ≫ (iF.inv ≫ e.hom.app F ≫ tF) ≫ (st y).map f.hom
  erw [← Category.assoc gF ((st x).map tf.hom), hg, Category.assoc]
  change tf.hom.app (op U) ≫ iG.hom ≫ iG.inv ≫ e.hom.app G ≫ tG =
    iF.hom ≫ (iF.inv ≫ e.hom.app F ≫ tF) ≫ (st y).map f.hom
  simp only [Iso.hom_inv_id_assoc]
  erw [Category.assoc iF.inv (e.hom.app F ≫ tF), Iso.hom_inv_id_assoc iF,
    Category.assoc (e.hom.app F) tF, ht]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ tG) hn).trans (Category.assoc _ _ _))

private theorem bandCohomologySectionsIso_hom_map {r : ℝ} (hr : 0 ≤ r) (d : ℤ) (F : Sh)
    {V U : Opens realLine} (h : V ≤ U) (hV : (V : Set ℝ).OrdConnected)
    (hU : (U : Set ℝ).OrdConnected) :
    ((Coh[r,d]).obj F).presheaf.map (homOfLE h).op ≫
        ((bandCohomologySectionsIso k r d V hV).app F).hom =
      ((bandCohomologySectionsIso k r d U hU).app F).hom ≫
        F.presheaf.map (homOfLE (bandOpen_mono_right r h)).op := by
  let e := ((bandCohomologyShiftIso k r d).app F).hom.hom
  change ((Coh[r,d]).obj F).presheaf.map (homOfLE h).op ≫
      e.app (op V) ≫ (H0TSectionsIso k r F V hV).hom =
    (e.app (op U) ≫ (H0TSectionsIso k r F U hU).hom) ≫
        F.presheaf.map (homOfLE (bandOpen_mono_right r h)).op
  erw [← Category.assoc, e.naturality (homOfLE h).op,
    Category.assoc, H0TSectionsIso_hom_map hr F h hV hU]
  simp only [H0TSectionsIso, Category.assoc]

/-- Shrinking the comparison open preserves the stalk identification whenever
the germ isomorphisms hold on both opens. -/
theorem bandCohomologyStalkIso_hom_eq_of_le {r : ℝ} (hr : 0 ≤ r) (d : ℤ) (F : Sh)
    {V U : Opens realLine} (h : V ≤ U) (hV : (V : Set ℝ).OrdConnected)
    (hU : (U : Set ℝ).OrdConnected) {x y : ℝ} (hx : x ∈ V) (hy : y ∈ bandOpen r V)
    [germV : IsIso (((Coh[r,d]).obj F).presheaf.germ V x hx)]
    [germU : IsIso (((Coh[r,d]).obj F).presheaf.germ U x (h hx))]
    [IsIso (F.presheaf.germ (bandOpen r V) y hy)]
    [IsIso (F.presheaf.germ (bandOpen r U) y (bandOpen_mono_right r h hy))] :
    (bandCohomologyStalkIso r d F V hV hx hy).hom =
      (bandCohomologyStalkIso r d F U hU (h hx) (bandOpen_mono_right r h hy)).hom := by
  let gV := ((Coh[r,d]).obj F).presheaf.germ V x hx
  let gU := ((Coh[r,d]).obj F).presheaf.germ U x (h hx)
  let : IsIso gV := germV
  let : IsIso gU := germU
  let tV := F.presheaf.germ (bandOpen r V) y hy
  let tU := F.presheaf.germ (bandOpen r U) y (bandOpen_mono_right r h hy)
  let eV := ((bandCohomologySectionsIso k r d V hV).app F).hom
  let eU := ((bandCohomologySectionsIso k r d U hU).app F).hom
  have hg : ((Coh[r,d]).obj F).presheaf.map (homOfLE h).op ≫ gV = gU :=
    TopCat.Presheaf.germ_res _ (homOfLE h) x hx
  have ht : F.presheaf.map (homOfLE (bandOpen_mono_right r h)).op ≫ tV = tU :=
    TopCat.Presheaf.germ_res F.presheaf (homOfLE (bandOpen_mono_right r h)) y hy
  change inv gV ≫ eV ≫ tV = inv gU ≫ eU ≫ tU
  apply (cancel_epi gU).mp
  erw [IsIso.hom_inv_id_assoc, ← hg, Category.assoc, IsIso.hom_inv_id_assoc,
    ← Category.assoc, bandCohomologySectionsIso_hom_map hr d F h hV hU, Category.assoc, ht]

end TDA.Sheaf.BandConvolution
