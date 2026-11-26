import TDA.Sheaf.RealConstructible
import TDA.Sheaf.RealStratificationExamples
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Fixtures for constructible sheaves on the real line

* No breakpoints: a constructible sheaf is a locally constant sheaf with finite-dimensional
  stalks, `Γ F` is the global sections `F(ℝ)`, and two such sheaves are isomorphic as soon as
  their global sections are. The extension of the one-vertex interval has one-dimensional global
  sections.
* One breakpoint at `0`, strata `0 ← 1 → 2`: for every interval `J` of the path, the explicit
  sheaf `Φ (interval J)` is constructible, has `Γ ≅ interval J`, and has the dimension of `J` at
  each star. The segments `[0, 1]` (`leftClosed`, the field on `(-∞, 0]`) and `[1, 2]`
  (`rightClosed`, the field on `[0, ∞)`) have one noninvertible restriction each, on opposite
  sides, and `[1, 1]` (`pointSheaf`) has two.
* Mathlib's skyscraper sheaf `skyscraperSheaf 0 k` is constructible for the breakpoint `0`, its
  sections over the stars form the interval `[1, 1]` (`sectionsSkyIso`), and it is therefore
  isomorphic to the extension of that interval (`skyIsoPointSheaf`).

Constructibility uses the interval-local `IsLocallyConstantOn` of `TDA.Sheaf.LocalSystem`; its
intended equivalence with "locally isomorphic to a constant sheaf" is not yet proved in Lean
(#1250).
-/

namespace TDA.Sheaf.RealConstructibleExamples

open CategoryTheory Limits TopologicalSpace Opposite TDA.Persistence
  TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealStratification TDA.Sheaf.LocalSystem
  TDA.Sheaf.RealConstructible TDA.Sheaf.RealStratificationExamples

variable (k : Type) [Field k]

/-- An interval diagram vanishes outside its segment. -/
private theorem isZero_interval_obj {n : ℕ} {o : Fin n → Bool} {J : FiniteInterval (n + 1)}
    {j : Fin (n + 1)} (hj : ¬J.alive j) : IsZero ((interval (k := k) o J).obj (vtx o j)) := by
  have : Subsingleton ((interval (k := k) o J).obj (vtx o j)) :=
    ⟨fun a b => Subtype.ext ((fiber_val_eq_zero hj a).trans (fiber_val_eq_zero hj b).symm)⟩
  exact ModuleCat.isZero_of_subsingleton _

/-! ### No breakpoints -/

/-- No breakpoints. -/
def p₀ : Fin 0 → ℝ := Fin.elim0

theorem p₀_strictMono : StrictMono p₀ := Subsingleton.strictMono p₀

theorem breakpoints_p₀ : breakpoints p₀ = ∅ := by
  simp [breakpoints]

/-- Without breakpoints every star is the whole line. -/
theorem star_p₀ (v : Fin (2 * 0 + 1)) : star p₀ v = ⊤ :=
  top_unique fun _ _ i => i.elim0

/-- Without breakpoints, constructible means locally constant on `ℝ` with finite-dimensional
stalks.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
theorem isConstructible_p₀_iff {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} :
    IsConstructible (breakpoints p₀) F ↔
      IsLocallyConstantOn F Set.univ ∧ ∀ x : ℝ, FiniteDimensional k (F.presheaf.stalk x) := by
  rw [IsConstructible, breakpoints_p₀, Finset.coe_empty, Set.compl_empty]

/-- Without breakpoints, `Γ F` is the global sections. -/
theorem sections_p₀ (F : TopCat.Sheaf (ModuleCat.{0} k) realLine) :
    ((sections k p₀).obj F).obj (vtx (orient 0) 0) = F.presheaf.obj (op ⊤) := by
  rw [sections_obj_obj, star_p₀]

/-- Without breakpoints, constructible sheaves with isomorphic global sections are isomorphic.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
theorem nonempty_iso_of_iso_top (F G : Constructible k p₀)
    (e : F.obj.presheaf.obj (op ⊤) ≅ G.obj.presheaf.obj (op ⊤)) : Nonempty (F ≅ G) := by
  have hF : ∀ X : Paths (Vertex (orient 0)),
      ((sections k p₀).obj F.obj).obj X = F.obj.presheaf.obj (op ⊤) := fun X =>
    congrArg (fun U => F.obj.presheaf.obj (op U)) (star_p₀ X)
  have hG : ∀ X : Paths (Vertex (orient 0)),
      ((sections k p₀).obj G.obj).obj X = G.obj.presheaf.obj (op ⊤) := fun X =>
    congrArg (fun U => G.obj.presheaf.obj (op U)) (star_p₀ X)
  refine ⟨(equivalence k p₀_strictMono).fullyFaithfulFunctor.preimageIso
    (ObjectProperty.isoMk _ (isoMk (fun X => eqToIso (hF X) ≪≫ e ≪≫ eqToIso (hG X).symm) ?_))⟩
  intro i j h
  obtain ⟨a, -, -⟩ := h
  exact a.elim0

/-- The constant sheaf without breakpoints: the extension of the one-vertex interval. -/
noncomputable def constSheaf₀ : TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  (extension k p₀_strictMono).obj (interval (orient 0) ⟨0, 1, by decide, by decide⟩)

theorem isConstructible_constSheaf₀ : IsConstructible (breakpoints p₀) (constSheaf₀ k) :=
  isConstructible_extension k p₀_strictMono fun _ => inferInstance

/-- The constant sheaf without breakpoints has one-dimensional global sections. -/
theorem finrank_constSheaf₀_top :
    Module.finrank k ((constSheaf₀ k).presheaf.obj (op ⊤)) = 1 := by
  rw [← star_p₀ 0]
  exact (extensionStarIso k p₀_strictMono (interval (orient 0) ⟨0, 1, by decide, by decide⟩)
    0).toLinearEquiv.finrank_eq.trans ((finrank_interval_obj _ _).trans (by decide))

/-! ### One breakpoint -/

/-- The arrow `1 → 0` from the point to the left cell. -/
theorem arrow_one_zero : Arrow (orient 1) 1 0 := arrow_orient_iff.2 ⟨rfl, Or.inl rfl⟩

/-- The arrow `1 → 2` from the point to the right cell. -/
theorem arrow_one_two : Arrow (orient 1) 1 2 := arrow_orient_iff.2 ⟨rfl, Or.inr rfl⟩

/-- The explicit sheaf of an interval `J` of `0 ← 1 → 2`: its extension `Φ (interval J)`. -/
noncomputable abbrev intervalSheaf (J : FiniteInterval 3) :
    TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  (extension k p₁_strictMono).obj (interval (orient 1) J)

theorem isConstructible_intervalSheaf (J : FiniteInterval 3) :
    IsConstructible (breakpoints p₁) (intervalSheaf k J) :=
  isConstructible_extension k p₁_strictMono fun _ => inferInstance

/-- `Γ` of the sheaf of `J` is the interval `J`. -/
noncomputable def sectionsIntervalSheafIso (J : FiniteInterval 3) :
    (sections k p₁).obj (intervalSheaf k J) ≅ interval (orient 1) J :=
  (extensionSectionsIso k p₁_strictMono).app _

/-- Over the star of `v`, the sheaf of `J` has dimension one on `J` and zero elsewhere. -/
theorem finrank_intervalSheaf_star (J : FiniteInterval 3) (v : Fin 3) :
    Module.finrank k ((intervalSheaf k J).presheaf.obj (op (star p₁ v))) =
      if J.alive v then 1 else 0 := by
  rw [(extensionStarIso k p₁_strictMono _ v).toLinearEquiv.finrank_eq, finrank_interval_obj]

/-- The restriction of the sheaf of `J` from the star of the point to an adjacent cell is not
invertible when `J` contains the point but not the cell. -/
theorem not_isIso_intervalSheaf_map {J : FiniteInterval 3} {w : Fin 3}
    (h : Arrow (orient 1) 1 w) (h1 : J.alive 1) (hw : ¬J.alive w) :
    ¬IsIso ((intervalSheaf k J).presheaf.map (homOfLE (star_le_star_of_arrow p₁ h)).op) := by
  intro hi
  have e := (asIso ((intervalSheaf k J).presheaf.map
    (homOfLE (star_le_star_of_arrow p₁ h)).op)).toLinearEquiv.finrank_eq
  rw [finrank_intervalSheaf_star, finrank_intervalSheaf_star] at e
  simp [h1, hw] at e

/-- The segment `[0, 1]`: the field on `(-∞, 0]`. -/
def segLeft : FiniteInterval 3 := ⟨0, 2, by decide, by decide⟩

/-- The segment `[1, 2]`: the field on `[0, ∞)`. -/
def segRight : FiniteInterval 3 := ⟨1, 3, by decide, by decide⟩

/-- The sheaf of `[0, 1]`, the field on `(-∞, 0]`. -/
noncomputable abbrev leftClosed : TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  intervalSheaf k segLeft

/-- The sheaf of `[1, 2]`, the field on `[0, ∞)`. -/
noncomputable abbrev rightClosed : TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  intervalSheaf k segRight

/-- The sheaf of `[1, 1]`, the field at the point `0`. -/
noncomputable abbrev pointSheaf : TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  intervalSheaf k pointSegment

/-- The field on `(-∞, 0]` has dimensions `1, 1, 0` over the stars `(-∞, 0)`, `ℝ`, `(0, ∞)`. -/
theorem finrank_leftClosed :
    Module.finrank k ((leftClosed k).presheaf.obj (op (star p₁ 0))) = 1 ∧
      Module.finrank k ((leftClosed k).presheaf.obj (op (star p₁ 1))) = 1 ∧
      Module.finrank k ((leftClosed k).presheaf.obj (op (star p₁ 2))) = 0 :=
  ⟨(finrank_intervalSheaf_star k _ 0).trans (by decide),
    (finrank_intervalSheaf_star k _ 1).trans (by decide),
    (finrank_intervalSheaf_star k _ 2).trans (by decide)⟩

/-- The field on `[0, ∞)` has dimensions `0, 1, 1` over the stars `(-∞, 0)`, `ℝ`, `(0, ∞)`. -/
theorem finrank_rightClosed :
    Module.finrank k ((rightClosed k).presheaf.obj (op (star p₁ 0))) = 0 ∧
      Module.finrank k ((rightClosed k).presheaf.obj (op (star p₁ 1))) = 1 ∧
      Module.finrank k ((rightClosed k).presheaf.obj (op (star p₁ 2))) = 1 :=
  ⟨(finrank_intervalSheaf_star k _ 0).trans (by decide),
    (finrank_intervalSheaf_star k _ 1).trans (by decide),
    (finrank_intervalSheaf_star k _ 2).trans (by decide)⟩

/-- For the field on `(-∞, 0]`, restriction from `ℝ` to the right cell `(0, ∞)` is not
invertible. -/
theorem not_isIso_leftClosed_right :
    ¬IsIso ((leftClosed k).presheaf.map
      (homOfLE (star_le_star_of_arrow p₁ arrow_one_two)).op) :=
  not_isIso_intervalSheaf_map k arrow_one_two (by decide) (by decide)

/-- For the field on `[0, ∞)`, restriction from `ℝ` to the left cell `(-∞, 0)` is not
invertible. -/
theorem not_isIso_rightClosed_left :
    ¬IsIso ((rightClosed k).presheaf.map
      (homOfLE (star_le_star_of_arrow p₁ arrow_one_zero)).op) :=
  not_isIso_intervalSheaf_map k arrow_one_zero (by decide) (by decide)

/-- For the field at the point, neither restriction from `ℝ` to a cell is invertible. -/
theorem not_isIso_pointSheaf :
    ¬IsIso ((pointSheaf k).presheaf.map
        (homOfLE (star_le_star_of_arrow p₁ arrow_one_zero)).op) ∧
      ¬IsIso ((pointSheaf k).presheaf.map
        (homOfLE (star_le_star_of_arrow p₁ arrow_one_two)).op) :=
  ⟨not_isIso_intervalSheaf_map k arrow_one_zero (by decide) (by decide),
    not_isIso_intervalSheaf_map k arrow_one_two (by decide) (by decide)⟩

/-! ### The skyscraper sheaf -/

open Classical in
/-- Mathlib's skyscraper sheaf at `0` with value `k`. -/
noncomputable def sky : TopCat.Sheaf (ModuleCat.{0} k) realLine :=
  skyscraperSheaf (0 : ℝ) (ModuleCat.of k k)

/-- Sections of the skyscraper over an open containing `0` are the field. -/
noncomputable def skyObjIso {U : Opens realLine} (h : (0 : ℝ) ∈ U) :
    (sky k).presheaf.obj (op U) ≅ ModuleCat.of k k :=
  eqToIso (ite_eq_left h)

open Classical in
/-- Sections of the skyscraper over an open missing `0` vanish. -/
theorem isZero_sky_obj {U : Opens realLine} (h : (0 : ℝ) ∉ U) :
    IsZero ((sky k).presheaf.obj (op U)) := by
  change IsZero ((skyscraperPresheaf (X := realLine) (0 : ℝ) (ModuleCat.of k k)).obj (op U))
  rw [skyscraperPresheaf_obj, ite_eq_right h]
  exact IsZero.of_iso (isZero_zero _)
    (terminalIsTerminal.uniqueUpToIso (isZero_zero _).isTerminal)

open Classical in
/-- The skyscraper is constructible for the breakpoint `0`: its sections vanish on opens
missing `0`, its stalk at `0` is the field and its other stalks vanish.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
theorem isConstructible_sky : IsConstructible (breakpoints p₁) (sky k) := by
  rw [IsConstructible, breakpoints_p₁, Finset.coe_singleton]
  refine ⟨fun x hx => ⟨⟨({0} : Set ℝ)ᶜ, isOpen_compl_singleton⟩, hx, subset_rfl,
    fun V W hVW _ _ _ hWN => ?_⟩, fun x => ?_⟩
  · have hW : (0 : ℝ) ∉ W := fun h => hWN h rfl
    exact isIso_of_source_target_iso_zero _ (isZero_sky_obj k hW).isoZero
      (isZero_sky_obj k fun h => hW (hVW h)).isoZero
  · by_cases hx : (0 : ℝ) = x
    · subst hx
      exact (skyscraperPresheafStalkOfSpecializes (X := realLine) (0 : ℝ) (ModuleCat.of k k)
        specializes_rfl).toLinearEquiv.symm.finiteDimensional
    · have hz : IsZero ((sky k).presheaf.stalk x) := IsZero.of_iso (isZero_zero _)
        ((skyscraperPresheafStalkOfNotSpecializesIsTerminal (X := realLine) (0 : ℝ)
          (ModuleCat.of k k) (specializes_iff_eq.not.2 hx)).uniqueUpToIso
          (isZero_zero _).isTerminal)
      have : Subsingleton ((sky k).presheaf.stalk x) := ModuleCat.subsingleton_of_isZero hz
      infer_instance

/-- **`Γ` of the skyscraper is the interval `[1, 1]`.** -/
noncomputable def sectionsSkyIso : (sections k p₁).obj (sky k) ≅ pointDiagram k := by
  classical
  refine isoMk (fun X => if h : (0 : ℝ) ∈ star p₁ X then ?_ else ?_) ?_
  · have hX : pointSegment.alive X := by
      have := (apply_mem_star_iff p₁_strictMono 0).1 h
      change 1 ≤ (X : Fin 3).val ∧ (X : Fin 3).val < 2
      simp only [Fin.val_zero] at this
      omega
    exact skyObjIso k h ≪≫ (LinearEquiv.ofTop _ (by
      simp [FiniteInterval.fiber, hX])).symm.toModuleIso
  · refine (isZero_sky_obj k h).iso (isZero_interval_obj k ?_)
    intro hX
    change 1 ≤ (X : Fin 3).val ∧ (X : Fin 3).val < 2 at hX
    exact h ((apply_mem_star_iff p₁_strictMono 0).2 (by simp only [Fin.val_zero]; omega))
  · intro i j h
    apply (isZero_interval_obj k _).eq_of_tgt
    rw [arrow_orient_iff] at h
    have := (i : Fin 3).isLt
    change ¬(1 ≤ (j : Fin 3).val ∧ (j : Fin 3).val < 2)
    omega

/-- The skyscraper is the extension of the interval `[1, 1]`, as constructible sheaves.
Local constancy is the interval-local `IsLocallyConstantOn`, not yet proved in Lean to be
equivalent to "locally isomorphic to a constant sheaf" (#1250). -/
noncomputable def skyIsoPointSheaf :
    (⟨sky k, isConstructible_sky k⟩ : Constructible k p₁) ≅
      ⟨pointSheaf k, isConstructible_intervalSheaf k pointSegment⟩ :=
  (equivalence k p₁_strictMono).fullyFaithfulFunctor.preimageIso
    (ObjectProperty.isoMk _ (sectionsSkyIso k ≪≫ (sectionsIntervalSheafIso k pointSegment).symm))

end TDA.Sheaf.RealConstructibleExamples
