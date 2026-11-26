import TDA.Sheaf.RayLocalization
import TDA.Sheaf.RaySheafExamples
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Ray localization: fixtures

These fixtures consume `TDA.Sheaf.RayLocalization` over a field `k`, with value category
`ModuleCat.{0} k`.

* `setModule S` is `k` on an order-connected set `S ⊆ ℝ`, with identity maps inside `S` and
  zero elsewhere; `setInclusion` is the inclusion `setModule I ⟶ setModule J` for `I ⊆ J`
  when `J` adds no point above a point of `I`.
* The endpoint alteration `alteration : setModule (Ioo 0 1) ⟶ setModule (Ico 0 1)` closes the
  left endpoint. It is not an isomorphism (`not_isIso_alteration`), while its image under `Q` is
  (`isIso_rayQ_map_alteration`), by `isIso_rayQ_map_iff`: its kernel is zero and its cokernel is
  ephemeral (`rayEphemeral_cokernel_alteration`).
* The positive interval `setModule (Ico 0 1)` is not ephemeral and `Q` of it is nonzero
  (`not_isZero_rayQ_setModule_Ico`).
* The singleton module `pointModule` of `TDA.Sheaf.RaySheafExamples` is ephemeral
  (`rayEphemeral_pointModule`) and nonzero, and `Q` of it is zero.
-/

set_option autoImplicit false

namespace TDA.Sheaf.RayLocalizationExamples

open CategoryTheory Limits TDA.Persistence TDA.Sheaf.RaySheaf TDA.Sheaf.RaySheafExamples

variable {k : Type} [Field k]

/-! ## Modules supported on an order-connected set -/

/-- The fibre of `setModule S`: `k` on `S` and zero elsewhere. -/
noncomputable def setFiber (S : Set ℝ) (t : ℝ) : Submodule k k := by
  classical
  exact if t ∈ S then ⊤ else ⊥

/-- The structure map of `setModule S`: the identity inside `S`, zero otherwise. -/
noncomputable def setMap (S : Set ℝ) {s t : ℝ} (_h : s ≤ t) :
    setFiber (k := k) S s →ₗ[k] setFiber (k := k) S t := by
  classical
  exact if h : s ∈ S ∧ t ∈ S then Submodule.inclusion (by simp [setFiber, h.1, h.2]) else 0

/-- The module `k` supported on an order-connected set `S`. -/
noncomputable def setModule (S : Set ℝ) [S.OrdConnected] : PModule.{0,0,0} k ℝ where
  obj t := ModuleCat.of k (setFiber (k := k) S t)
  map f := ModuleCat.ofHom (setMap S (leOfHom f))
  map_id t := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change setFiber (k := k) S t at x
    change setMap (k := k) S (leOfHom (𝟙 t)) x = x
    apply Subtype.ext
    by_cases h : t ∈ S
    · simp [setMap, h]
    · have hx : (x : k) = 0 := by
        simpa [setFiber, h] using x.property
      simp [setMap, h, hx]
  map_comp {s t r} f g := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases hs : s ∈ S
    · by_cases hr : r ∈ S
      · have ht : t ∈ S := Set.OrdConnected.out ‹_› hs hr ⟨leOfHom f, leOfHom g⟩
        simp [setMap, hs, ht, hr]
      · simp [setMap, hr]
    · simp [setMap, hs]

/-- Outside `S`, the maps of `setModule S` vanish. -/
theorem setModule_map_eq_zero (S : Set ℝ) [S.OrdConnected] {s t : ℝ} (f : s ⟶ t)
    (h : ¬ (s ∈ S ∧ t ∈ S)) : (setModule (k := k) S).map f = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change setMap (k := k) S (leOfHom f) x = 0
  simp only [setMap, h, dite_false]
  rfl

/-- Inside `S`, the maps of `setModule S` are the identity of `k` on elements. -/
theorem setModule_map_apply (S : Set ℝ) [S.OrdConnected] {s t : ℝ} (f : s ⟶ t) (hs : s ∈ S)
    (ht : t ∈ S) (x : setFiber (k := k) S s) :
    (show setFiber (k := k) S t from ((setModule (k := k) S).map f).hom x).1 = (x : k) := by
  classical
  change ((setMap (k := k) S (leOfHom f) x : setFiber S t) : k) = _
  simp [setMap, hs, ht]

/-- The fibres of `setModule` are monotone in the support. -/
theorem setFiber_mono {I J : Set ℝ} (hIJ : I ⊆ J) (t : ℝ) :
    setFiber (k := k) I t ≤ setFiber (k := k) J t := by
  classical
  by_cases h : t ∈ I
  · simp [setFiber, h, hIJ h]
  · simp [setFiber, h]

/-- The inclusion `setModule I ⟶ setModule J` for `I ⊆ J`, when every point of `J` above a
point of `I` lies in `I`. -/
noncomputable def setInclusion {I J : Set ℝ} [I.OrdConnected] [J.OrdConnected] (hIJ : I ⊆ J)
    (hup : ∀ s t : ℝ, s ≤ t → s ∈ I → t ∈ J → t ∈ I) :
    setModule (k := k) I ⟶ setModule J where
  app t := ModuleCat.ofHom (Submodule.inclusion (setFiber_mono hIJ t))
  naturality s t f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change setFiber (k := k) I s at x
    change ((setMap (k := k) I (leOfHom f) x : setFiber I t) : k) =
      ((setMap (k := k) J (leOfHom f) (Submodule.inclusion (setFiber_mono hIJ s) x) :
        setFiber J t) : k)
    by_cases hs : s ∈ I
    · by_cases ht : t ∈ I
      · simp [setMap, hs, ht, hIJ hs, hIJ ht]
      · have htJ : t ∉ J := fun h => ht (hup s t (leOfHom f) hs h)
        simp [setMap, ht, htJ]
    · have hx : (x : k) = 0 := by
        simpa [setFiber, hs] using x.property
      by_cases hJ : s ∈ J ∧ t ∈ J
      · simp [setMap, hs, hJ, hx]
      · simp [setMap, hs, hJ]

/-- The inclusion is a monomorphism. -/
theorem mono_setInclusion {I J : Set ℝ} [I.OrdConnected] [J.OrdConnected] (hIJ : I ⊆ J)
    (hup : ∀ s t : ℝ, s ≤ t → s ∈ I → t ∈ J → t ∈ I) :
    Mono (setInclusion (k := k) hIJ hup) := by
  have : ∀ t, Mono ((setInclusion (k := k) hIJ hup).app t) := fun t =>
    (ModuleCat.mono_iff_injective _).2 (Submodule.inclusion_injective (setFiber_mono hIJ t))
  exact NatTrans.mono_of_mono_app _

/-- At a point of `I`, the inclusion is an epimorphism. -/
theorem epi_setInclusion_app {I J : Set ℝ} [I.OrdConnected] [J.OrdConnected] (hIJ : I ⊆ J)
    (hup : ∀ s t : ℝ, s ≤ t → s ∈ I → t ∈ J → t ∈ I) {t : ℝ} (ht : t ∈ I) :
    Epi ((setInclusion (k := k) hIJ hup).app t) := by
  classical
  refine (ModuleCat.epi_iff_surjective _).2 fun y => ?_
  change setFiber (k := k) J t at y
  exact ⟨⟨y.1, by simp [setFiber, ht]⟩, rfl⟩

/-! ## The endpoint alteration -/

/-- Closing the left endpoint: the inclusion `setModule (Ioo 0 1) ⟶ setModule (Ico 0 1)`. -/
noncomputable def alteration : setModule (k := k) (Set.Ioo 0 1) ⟶ setModule (Set.Ico 0 1) :=
  setInclusion Set.Ioo_subset_Ico_self fun _ _ hst hs ht =>
    ⟨hs.1.trans_le hst, ht.2⟩

/-- The endpoint alteration is not an isomorphism: at `0` it is `0 ⟶ k`. -/
theorem not_isIso_alteration : ¬ IsIso (alteration (k := k)) := by
  classical
  intro h
  have h1 : (1 : k) ∈ setFiber (k := k) (Set.Ico 0 1) 0 := by simp [setFiber]
  let y : setFiber (k := k) (Set.Ioo 0 1) 0 := ((inv (alteration (k := k))).app 0).hom ⟨1, h1⟩
  have hy : (y : k) = 0 := by simpa [setFiber] using y.property
  have hxy : (show setFiber (k := k) (Set.Ico 0 1) 0 from
      ((alteration (k := k)).app 0).hom y) = ⟨1, h1⟩ :=
    congrArg (fun φ => (φ.app 0).hom ⟨1, h1⟩) (IsIso.inv_hom_id (alteration (k := k)))
  exact one_ne_zero ((congrArg Subtype.val hxy).symm.trans hy)

/-- The cokernel of the endpoint alteration is ephemeral: it lives at the added endpoint. -/
theorem rayEphemeral_cokernel_alteration :
    rayEphemeral _ (cokernel (alteration (k := k))) := by
  intro s t hst
  have key : (setModule (k := k) (Set.Ico 0 1)).map (homOfLE hst.le) ≫
      (cokernel.π (alteration (k := k))).app t = 0 := by
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
    · have : Epi ((alteration (k := k)).app t) := epi_setInclusion_app _ _ ht
      have hz : (cokernel.π (alteration (k := k))).app t = 0 := by
        rw [← cancel_epi ((alteration (k := k)).app t), comp_zero]
        exact congrArg (fun φ => φ.app t) (cokernel.condition (alteration (k := k)))
      rw [hz, comp_zero]
    · rw [setModule_map_eq_zero _ _ fun h => ht ⟨h.1.1.trans_lt hst, h.2.2⟩, zero_comp]
  rw [← cancel_epi ((cokernel.π (alteration (k := k))).app s), comp_zero,
    ← (cokernel.π (alteration (k := k))).naturality]
  exact key

/-- `Q` turns the endpoint alteration into an isomorphism. -/
theorem isIso_rayQ_map_alteration :
    IsIso ((rayQ (ModuleCat.{0} k)).map (alteration (k := k))) := by
  have : Mono (alteration (k := k)) := mono_setInclusion _ _
  rw [isIso_rayQ_map_iff]
  exact ⟨fun s _ _ => ((isZero_kernel_of_mono _).obj s).eq_of_src _ _,
    rayEphemeral_cokernel_alteration⟩

/-- The localization functor at the isomorphisms modulo ephemeral modules inverts the endpoint
alteration. -/
example : IsIso ((rayEphemeral (ModuleCat.{0} k)).isoModSerre.Q.map (alteration (k := k))) :=
  Localization.inverts _ (rayEphemeral _).isoModSerre _
    ((isIso_rayQ_map_iff _).1 isIso_rayQ_map_alteration)

/-! ## A positive interval and a singleton -/

/-- `Q` of the positive interval `[0, 1)` is nonzero: its map from `0` to `1/2` is the identity. -/
theorem not_isZero_rayQ_setModule_Ico :
    ¬ IsZero ((rayQ (ModuleCat.{0} k)).obj (setModule (k := k) (Set.Ico 0 1))) := by
  classical
  rw [← rayEphemeral_iff]
  intro h
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  have hh : (1 / 2 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1 : (1 : k) ∈ setFiber (k := k) (Set.Ico 0 1) 0 := by simp [setFiber, h0]
  have := congrArg (fun φ : (setModule (k := k) (Set.Ico 0 1)).obj 0 ⟶ _ =>
    (show setFiber (k := k) (Set.Ico 0 1) (1 / 2) from φ.hom ⟨1, h1⟩).1)
      (h 0 (1 / 2) (by norm_num))
  rw [setModule_map_apply _ _ h0 hh] at this
  exact one_ne_zero this

/-- The positive interval `[0, 1)` is not ephemeral. -/
example : ¬ rayEphemeral _ (setModule (k := k) (Set.Ico 0 1)) :=
  fun h => not_isZero_rayQ_setModule_Ico ((rayEphemeral_iff _).1 h)

/-- The singleton module is ephemeral. -/
theorem rayEphemeral_pointModule : rayEphemeral _ (pointModule (k := k)) :=
  fun _ _ h => pointModule_map_lt h

/-- The singleton module is nonzero, and `Q` of it is zero. -/
example : ¬ IsZero (pointModule (k := k)) ∧
    IsZero ((rayQ (ModuleCat.{0} k)).obj (pointModule (k := k))) :=
  ⟨not_isZero_pointModule, (rayEphemeral_iff _).1 rayEphemeral_pointModule⟩

end TDA.Sheaf.RayLocalizationExamples
