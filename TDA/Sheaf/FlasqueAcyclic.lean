import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Order.Zorn
import TDA.Sheaf.PointSheaf
import TDA.Sheaf.PresheafRestriction
import TDA.Sheaf.RightDerivedHomology

/-!
# Flasque sheaves of modules are acyclic for direct images

Let `k` be a ring and `X : TopCat`. Mathlib's `TopCat.Sheaf.IsFlasque` (every restriction map is
an epimorphism) applies to sheaves of `k`-modules, but its acyclicity results are stated for
sheaves of abelian groups only at the pinned Mathlib. This file proves them for
`X.Sheaf (ModuleCat k)`.

* `sections_exact_of_left_exact`: for an exact complex `X₁ ⟶ X₂ ⟶ X₃` with `X₁ ⟶ X₂` a
  monomorphism, sections over each open are exact at `X₂`.
* `epi_of_shortExact`: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₁` flasque,
  `X₂(U) ⟶ X₃(U)` is surjective for every open `U`. The proof is Mathlib's Zorn argument: a
  maximal partial lift of a section of `X₃` is defined on all of `U`, because a local lift near
  a further point differs from it by a section of `X₁`, which extends by flasqueness.
* `isFlasque_of_shortExact`: if `X₁` and `X₂` are flasque, so is `X₃`.
* `isFlasque_of_iso`, `isFlasque_of_isZero`, `isFlasque_of_id_eq_add` and the instance
  `isFlasque_biprod`: flasqueness passes along isomorphisms, holds for zero sheaves and for
  retracts of a sum of two flasque sheaves (such as their biproduct).
* `pushforward_shortExact_of_isFlasque`: the direct image `f_*` keeps a short exact sequence
  with flasque kernel short exact.
* `acyclic_pushforward_of_isFlasque`: `f_*` keeps a bounded below acyclic complex of flasque
  sheaves acyclic (its cycle sheaves are flasque, by induction from the bottom), and
  `quasiIso_pushforward_of_isFlasque`: `f_*` keeps a quasi-isomorphism between bounded below
  complexes of flasque sheaves a quasi-isomorphism (through the mapping cone).
* `isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque`: for a bounded below complex `K` of
  flasque sheaves, the comparison `f_* K ⟶ Rf_* K` in `D⁺` is an isomorphism, so flasque
  complexes compute `Rf_*`. The case of global sections, `f = toPt X`, is
  `isIso_rightDerivedFunctorPlusUnit_app_toPt_of_isFlasque`.

Derived categories are instance arguments `[HasDerivedCategory (X.Sheaf (ModuleCat k))]`, as in
`TDA.Sheaf.DerivedPlus`.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite

namespace TDA.Sheaf

variable {k : Type} [Ring k] {X : TopCat.{0}}

section sections

/-- **Left exactness on sections.** If `X₁ ⟶ X₂ ⟶ X₃` is exact and `X₁ ⟶ X₂` is a monomorphism of
sheaves of `k`-modules, a section of `X₂` over `U` killed by `X₂ ⟶ X₃` comes from a section of
`X₁` over `U`. -/
theorem sections_exact_of_left_exact {S : ShortComplex (X.Sheaf (ModuleCat.{0} k))}
    (hS : S.Exact) [Mono S.f] {U : Opens X} (s : S.X₂.presheaf.obj (op U))
    (hs : S.g.hom.app _ s = 0) : ∃ t : S.X₁.presheaf.obj (op U), S.f.hom.app _ t = s := by
  let G := TopCat.Sheaf.forget (ModuleCat.{0} k) X
  have key₁ : PreservesFiniteLimits G → ∀ S : ShortComplex (X.Sheaf (ModuleCat.{0} k)),
      S.Exact ∧ Mono S.f → (S.map G).Exact ∧ Mono (G.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae G).out 4 2).1
  obtain ⟨h₁, h₂⟩ := key₁ inferInstance S ⟨hS, inferInstance⟩
  -- Sections over `U`: evaluation at `U` is exact on presheaves.
  let E := (evaluation (Opens X)ᵒᵖ (ModuleCat.{0} k)).obj (op U)
  have key₂ : PreservesFiniteLimits E → ∀ T : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} k),
      T.Exact ∧ Mono T.f → (T.map E).Exact ∧ Mono (E.map T.f) :=
    ((Functor.preservesFiniteLimits_tfae E).out 4 2).1
  have h := key₂ inferInstance _ ⟨h₁, h₂⟩
  exact (ShortComplex.moduleCat_exact_iff _).1 h.1 s hs

end sections

section epi

/-- A lift of the restriction of a section `s` of `S.X₃` over `U` to an open `V ≤ U`, along
`S.g`. -/
private structure PartialLift (S : ShortComplex (X.Sheaf (ModuleCat.{0} k))) (U : Opens X)
    (s : S.X₃.presheaf.obj (op U)) where
  V : Opens X
  le : V ≤ U
  t : S.X₂.presheaf.obj (op V)
  ht : S.g.hom.app _ t = S.X₃.presheaf.map (homOfLE le).op s

variable {S : ShortComplex (X.Sheaf (ModuleCat.{0} k))} {U : Opens X}
  {s : S.X₃.presheaf.obj (op U)}

/-- `b` extends `a`: its open contains that of `a` and it restricts to `a` there. -/
private def PartialLift.Ext (a b : PartialLift S U s) : Prop :=
  ∃ h : a.V ≤ b.V, S.X₂.presheaf.map (homOfLE h).op b.t = a.t

private theorem PartialLift.ext_trans {a b c : PartialLift S U s} (hab : a.Ext b)
    (hbc : b.Ext c) : a.Ext c := by
  obtain ⟨h₁, e₁⟩ := hab
  obtain ⟨h₂, e₂⟩ := hbc
  exact ⟨h₁.trans h₂, by rw [← presheaf_map_map_apply _ h₁ h₂, e₂, e₁]⟩

/-- A chain of partial lifts has an upper bound: glue the lifts over the union of their
opens. -/
private theorem PartialLift.exists_ub (c : Set (PartialLift S U s))
    (hc : IsChain PartialLift.Ext c) : ∃ ub, ∀ a ∈ c, a.Ext ub := by
  let Uf : c → Opens X := fun a => a.1.V
  have hcompat : TopCat.Presheaf.IsCompatible S.X₂.presheaf Uf (fun a => a.1.t) := by
    intro a b
    rcases eq_or_ne a b with rfl | hab
    · rfl
    rcases hc a.2 b.2 (fun h => hab (Subtype.ext h)) with ⟨h, e⟩ | ⟨h, e⟩
    · change S.X₂.presheaf.map (homOfLE _).op a.1.t = S.X₂.presheaf.map (homOfLE _).op b.1.t
      rw [← e, presheaf_map_map_apply]
    · change S.X₂.presheaf.map (homOfLE _).op a.1.t = S.X₂.presheaf.map (homOfLE _).op b.1.t
      rw [← e, presheaf_map_map_apply]
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing S.X₂ Uf (fun a => a.1.t) hcompat
  have hle : iSup Uf ≤ U := iSup_le fun a => a.1.le
  refine ⟨⟨iSup Uf, hle, t, ?_⟩, fun a ha => ⟨le_iSup Uf ⟨a, ha⟩, ht ⟨a, ha⟩⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq S.X₃ Uf _ _ fun a => ?_
  change S.X₃.presheaf.map (homOfLE (le_iSup Uf a)).op (S.g.hom.app _ t) =
    S.X₃.presheaf.map (homOfLE (le_iSup Uf a)).op (S.X₃.presheaf.map (homOfLE hle).op s)
  rw [← sheafHom_naturality_apply, presheaf_map_map_apply]
  change S.g.hom.app _ (S.X₂.presheaf.map (Opens.leSupr Uf a).op t) = _
  rw [ht a, a.1.ht]

end epi

/-- **Flasque kernels give surjections on sections.** Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short
exact sequence of sheaves of `k`-modules with `X₁` flasque. Then `X₂(U) ⟶ X₃(U)` is an
epimorphism, that is, surjective (`ModuleCat.epi_iff_surjective`), for every open `U`. This is
Mathlib's `TopCat.Sheaf.IsFlasque.epi_of_shortExact` for sheaves of modules. -/
theorem epi_of_shortExact {S : ShortComplex (X.Sheaf (ModuleCat.{0} k))} (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] (U : Opens X) : Epi (S.g.hom.app (op U)) := by
  have mm := presheaf_map_map_apply (k := k) (X := X)
  have nat := @sheafHom_naturality_apply k _ X
  have := hS.mono_f
  rw [ModuleCat.epi_iff_surjective]
  intro s
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded (PartialLift.exists_ub (S := S) (s := s))
    PartialLift.ext_trans
  have hUm : U ≤ m.V := by
    intro x hx
    have hloc := (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g
    obtain ⟨W, hWU, ⟨t₁, ht₁⟩, hxW⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).1 hloc U s x hx
    change S.g.hom.app _ t₁ = S.X₃.presheaf.map (homOfLE hWU).op s at ht₁
    -- The difference of `m` and the local lift `t₁` over `m.V ⊓ W` comes from `X₁`.
    let d := S.X₂.presheaf.map (homOfLE (inf_le_left : m.V ⊓ W ≤ m.V)).op m.t -
      S.X₂.presheaf.map (homOfLE (inf_le_right : m.V ⊓ W ≤ W)).op t₁
    have hd : S.g.hom.app _ d = 0 := by
      simp only [d, map_sub, nat, m.ht, ht₁, mm, sub_self]
    obtain ⟨c, hc⟩ := sections_exact_of_left_exact hS.exact d hd
    -- Flasqueness extends it over `W`; the corrected local lift glues with `m`.
    obtain ⟨c', hc'⟩ := (ModuleCat.epi_iff_surjective
      (S.X₁.presheaf.map (homOfLE (inf_le_right : m.V ⊓ W ≤ W)).op)).1 inferInstance c
    obtain ⟨σ, hσ₁, hσ₂⟩ := exists_glue₂ S.X₂ m.t (t₁ + S.f.hom.app _ c') (by
      rw [map_add, ← nat, hc', hc]
      simp only [d]
      abel)
    let a : PartialLift S U s := ⟨m.V ⊔ W, sup_le m.le hWU, σ, by
      refine TopCat.Sheaf.eq_of_locally_eq₂ S.X₃ (homOfLE le_sup_left) (homOfLE le_sup_right)
        le_rfl _ _ ?_ ?_
      · rw [← nat, hσ₁, m.ht, mm]
      · rw [← nat, hσ₂, map_add, shortComplex_g_f_apply, add_zero, ht₁, mm]⟩
    obtain ⟨h, -⟩ := hm a ⟨le_sup_left, hσ₁⟩
    exact h (le_sup_right (a := m.V) hxW)
  refine ⟨S.X₂.presheaf.map (homOfLE hUm).op m.t, ?_⟩
  rw [nat, m.ht, mm, presheaf_map_eq _ _ (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

/-- **Quotients of flasque sheaves by flasque sheaves are flasque.** In a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of sheaves of `k`-modules with `X₁` and `X₂` flasque, `X₃` is
flasque. -/
theorem isFlasque_of_shortExact {S : ShortComplex (X.Sheaf (ModuleCat.{0} k))}
    (hS : S.ShortExact) [TopCat.Sheaf.IsFlasque S.X₁] [TopCat.Sheaf.IsFlasque S.X₂] :
    TopCat.Sheaf.IsFlasque S.X₃ where
  epi {U V} i := by
    have : Epi (S.g.hom.app U ≫ S.X₃.presheaf.map i) := by
      rw [← S.g.hom.naturality i]
      exact epi_comp' inferInstance (epi_of_shortExact hS (unop V))
    exact epi_of_epi (S.g.hom.app U) _

section closure

/-- Flasqueness passes along isomorphisms of sheaves. -/
theorem isFlasque_of_iso {F G : X.Sheaf (ModuleCat.{0} k)} (e : F ≅ G)
    [TopCat.Sheaf.IsFlasque F] : TopCat.Sheaf.IsFlasque G where
  epi {U V} i := by
    rw [ModuleCat.epi_iff_surjective]
    intro s
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (F.presheaf.map i)).1 inferInstance
      (e.inv.hom.app V s)
    refine ⟨e.hom.hom.app U a, ?_⟩
    rw [← NatTrans.naturality_apply, ha]
    change (e.inv ≫ e.hom).hom.app V s = s
    rw [e.inv_hom_id]
    rfl

/-- A zero sheaf is flasque. -/
theorem isFlasque_of_isZero {F : X.Sheaf (ModuleCat.{0} k)} (hF : IsZero F) :
    TopCat.Sheaf.IsFlasque F where
  epi {_ V} _ :=
    IsZero.epi (Functor.map_isZero (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj V) hF) _

/-- A sheaf `B` with `𝟙 B = p₁ ≫ i₁ + p₂ ≫ i₂` for maps through flasque sheaves `A₁` and `A₂` is
flasque. -/
theorem isFlasque_of_id_eq_add {B A₁ A₂ : X.Sheaf (ModuleCat.{0} k)}
    [TopCat.Sheaf.IsFlasque A₁] [TopCat.Sheaf.IsFlasque A₂] (p₁ : B ⟶ A₁) (i₁ : A₁ ⟶ B)
    (p₂ : B ⟶ A₂) (i₂ : A₂ ⟶ B) (h : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 B) :
    TopCat.Sheaf.IsFlasque B where
  epi {U V} i := by
    rw [ModuleCat.epi_iff_surjective]
    intro s
    obtain ⟨a₁, ha₁⟩ := (ModuleCat.epi_iff_surjective (A₁.presheaf.map i)).1 inferInstance
      (p₁.hom.app V s)
    obtain ⟨a₂, ha₂⟩ := (ModuleCat.epi_iff_surjective (A₂.presheaf.map i)).1 inferInstance
      (p₂.hom.app V s)
    refine ⟨i₁.hom.app U a₁ + i₂.hom.app U a₂, ?_⟩
    rw [map_add, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ha₁, ha₂]
    have h' := congrArg (fun φ : B ⟶ B => φ.hom.app V s) h
    simp at h'
    exact h'

/-- The biproduct of two flasque sheaves is flasque. -/
instance isFlasque_biprod (A₁ A₂ : X.Sheaf (ModuleCat.{0} k)) [TopCat.Sheaf.IsFlasque A₁]
    [TopCat.Sheaf.IsFlasque A₂] : TopCat.Sheaf.IsFlasque (A₁ ⊞ A₂) :=
  isFlasque_of_id_eq_add biprod.fst biprod.inl biprod.snd biprod.inr biprod.total

end closure

section pushforward

variable {Y : TopCat.{0}}

/-- The direct image is left exact (a right adjoint). -/
private theorem preservesFiniteLimits_pushforward (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f) :=
  have := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k)
    f).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- **Direct images of short exact sequences with flasque kernel.** For a continuous map `f`,
the direct image `f_*` keeps a short exact sequence of sheaves of `k`-modules with flasque first
term short exact. -/
theorem pushforward_shortExact_of_isFlasque (f : X ⟶ Y)
    {S : ShortComplex (X.Sheaf (ModuleCat.{0} k))} (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque S.X₁] :
    (S.map (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f)).ShortExact := by
  let F := TopCat.Sheaf.pushforward (ModuleCat.{0} k) f
  have key : PreservesFiniteLimits F → ∀ S : ShortComplex (X.Sheaf (ModuleCat.{0} k)),
      S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae F).out 4 1).1
  have h := key (preservesFiniteLimits_pushforward f) S hS
  refine ShortComplex.ShortExact.mk' h.1 h.2 ?_
  have (V : (Opens Y)ᵒᵖ) : Epi (((sheafToPresheaf _ _).map (S.map F).g).app V) :=
    epi_of_shortExact hS ((Opens.map f).obj (unop V))
  exact (sheafToPresheaf _ _).epi_of_epi_map (NatTrans.epi_of_epi_app _)

end pushforward

section cycles

variable {A : Type*} [Category* A] [Abelian A]

/-- The short complex `Zⁱ ⟶ Cⁱ ⟶ Zʲ` of cycles of a cochain complex, for `i + 1 = j`. -/
private abbrev cyclesSc (C : CochainComplex A ℤ) (i j : ℤ) : ShortComplex A :=
  ShortComplex.mk (C.iCycles i) (C.toCycles i j) (by
    rw [← cancel_mono (C.iCycles j), Category.assoc, C.toCycles_i, C.iCycles_d, zero_comp])

/-- If a cochain complex is exact in degree `j = i + 1`, then `0 ⟶ Zⁱ ⟶ Cⁱ ⟶ Zʲ ⟶ 0` is short
exact. -/
private theorem cyclesSc_shortExact (C : CochainComplex A ℤ) {i j l : ℤ} (hij : i + 1 = j)
    (hjl : j + 1 = l) (hC : C.ExactAt j) : (cyclesSc C i j).ShortExact := by
  have hT : (ShortComplex.mk (C.iCycles i) (C.d i j) (C.iCycles_d i j)).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (C.cyclesIsKernel i j ((ComplexShape.up ℤ).next_eq' hij))
  let φ : cyclesSc C i j ⟶ ShortComplex.mk (C.iCycles i) (C.d i j) (C.iCycles_d i j) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := C.iCycles j }
  have hE : (C.sc' i j l).Exact :=
    (C.exactAt_iff' i j l ((ComplexShape.up ℤ).prev_eq' hij)
      ((ComplexShape.up ℤ).next_eq' hjl)).1 hC
  have := hE.epi_toCycles
  have heq : C.toCycles i j = (C.sc' i j l).toCycles ≫
      (C.cyclesIsoSc' i j l ((ComplexShape.up ℤ).prev_eq' hij)
        ((ComplexShape.up ℤ).next_eq' hjl)).inv := by
    rw [← C.toCycles_cyclesIsoSc'_hom i j l ((ComplexShape.up ℤ).prev_eq' hij)
      ((ComplexShape.up ℤ).next_eq' hjl), Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hT)
    (inferInstanceAs (Mono (C.iCycles i))) ?_
  change Epi (C.toCycles i j)
  rw [heq]
  infer_instance

/-- A morphism of cochain complexes is a quasi-isomorphism exactly when its mapping cone is
acyclic. -/
private theorem acyclic_mappingCone_iff {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (CochainComplex.mappingCone φ).Acyclic ↔ QuasiIso φ := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  refine ((HomotopyCategory.subcategoryAcyclic A).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)).symm.trans ?_
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff φ).trans
    (HomologicalComplex.mem_quasiIso_iff φ)

end cycles

section acyclic

variable {Y : TopCat.{0}}

/-- In a bounded below acyclic complex of flasque sheaves of `k`-modules, every cycle sheaf is
flasque. -/
private theorem isFlasque_cycles (C : CochainComplex (X.Sheaf (ModuleCat.{0} k)) ℤ) (n₀ : ℤ)
    [C.IsStrictlyGE n₀] [∀ n, TopCat.Sheaf.IsFlasque (C.X n)] (hC : C.Acyclic) (m : ℤ) :
    TopCat.Sheaf.IsFlasque (C.cycles m) := by
  have hzero (i : ℤ) (hi : i < n₀) : TopCat.Sheaf.IsFlasque (C.cycles i) :=
    isFlasque_of_isZero (IsZero.of_mono (C.iCycles i) (C.isZero_of_isStrictlyGE n₀ i hi))
  refine Int.inductionOn' m (n₀ - 1) (hzero _ (by omega)) (fun i _ hi => ?_)
    (fun i hi _ => hzero _ (by omega))
  have := cyclesSc_shortExact C (i := i) (j := i + 1) (l := i + 1 + 1) rfl rfl (hC (i + 1))
  exact isFlasque_of_shortExact this

/-- **Direct images of acyclic flasque complexes.** For a continuous map `f`, the direct image
`f_*` keeps a bounded below acyclic complex of flasque sheaves of `k`-modules acyclic. -/
theorem acyclic_pushforward_of_isFlasque (f : X ⟶ Y)
    (C : CochainComplex (X.Sheaf (ModuleCat.{0} k)) ℤ) (n₀ : ℤ) [C.IsStrictlyGE n₀]
    [∀ n, TopCat.Sheaf.IsFlasque (C.X n)] (hC : C.Acyclic) :
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapHomologicalComplex _).obj C).Acyclic := by
  let F := TopCat.Sheaf.pushforward (ModuleCat.{0} k) f
  intro j
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have := isFlasque_cycles C n₀ hC i
  have hS := pushforward_shortExact_of_isFlasque f
    (cyclesSc_shortExact C (i := i) (j := i + 1) (l := i + 1 + 1) rfl rfl (hC (i + 1)))
  rw [HomologicalComplex.exactAt_iff' _ i (i + 1) (i + 1 + 1)
    ((ComplexShape.up ℤ).prev_eq' rfl) ((ComplexShape.up ℤ).next_eq' rfl)]
  -- `F` keeps `Zⁱ⁺¹` the kernel of the differential.
  have key : PreservesFiniteLimits F → ∀ S : ShortComplex (X.Sheaf (ModuleCat.{0} k)),
      S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f) :=
    ((Functor.preservesFiniteLimits_tfae F).out 4 2).1
  have hT := key (preservesFiniteLimits_pushforward f)
    (ShortComplex.mk (C.iCycles (i + 1)) (C.d (i + 1) (i + 1 + 1)) (C.iCycles_d _ _))
    ⟨ShortComplex.exact_of_f_is_kernel _
      (C.cyclesIsKernel _ _ ((ComplexShape.up ℤ).next_eq' rfl)), inferInstance⟩
  let ψ : ((F.mapHomologicalComplex _).obj C).sc' i (i + 1) (i + 1 + 1) ⟶
      (ShortComplex.mk (C.iCycles (i + 1)) (C.d (i + 1) (i + 1 + 1))
        (C.iCycles_d _ _)).map F :=
    { τ₁ := F.map (C.toCycles i (i + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        simp only [ShortComplex.map_f, HomologicalComplex.shortComplexFunctor'_obj_f,
          Functor.mapHomologicalComplex_obj_d, Category.comp_id, ← F.map_comp, C.toCycles_i]
      comm₂₃ := by
        simp only [ShortComplex.map_g, HomologicalComplex.shortComplexFunctor'_obj_g,
          Functor.mapHomologicalComplex_obj_d, Category.comp_id, Category.id_comp] }
  have : Epi ψ.τ₁ := hS.epi_g
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2 hT.1

/-- **Direct images of quasi-isomorphisms of flasque complexes.** For a continuous map `f`, the
direct image `f_*` keeps a quasi-isomorphism between bounded below complexes of flasque sheaves
of `k`-modules a quasi-isomorphism. -/
theorem quasiIso_pushforward_of_isFlasque (f : X ⟶ Y)
    {K L : CochainComplex (X.Sheaf (ModuleCat.{0} k)) ℤ} (φ : K ⟶ L) [QuasiIso φ] (n₀ : ℤ)
    [K.IsStrictlyGE n₀] [L.IsStrictlyGE n₀] [∀ n, TopCat.Sheaf.IsFlasque (K.X n)]
    [∀ n, TopCat.Sheaf.IsFlasque (L.X n)] :
    QuasiIso (((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).mapHomologicalComplex _).map φ) := by
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (n₀ - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyGE n₀ _ (by omega), L.isZero_of_isStrictlyGE n₀ _ (by omega)⟩
  have (n : ℤ) : TopCat.Sheaf.IsFlasque ((CochainComplex.mappingCone φ).X n) :=
    isFlasque_of_id_eq_add _ _ _ _ (CochainComplex.mappingCone.id_X φ n (n + 1) rfl)
  have h := acyclic_pushforward_of_isFlasque f (CochainComplex.mappingCone φ) (n₀ - 1)
    ((acyclic_mappingCone_iff φ).2 inferInstance)
  rw [← acyclic_mappingCone_iff]
  exact fun n => (h n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ
      (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f))

end acyclic

section derived

variable {Y : TopCat.{0}} [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]

/-- **Flasque complexes compute derived direct images.** For a continuous map `f` and a bounded
below complex `K` of flasque sheaves of `k`-modules, the comparison `f_* K ⟶ Rf_* K` of the
derived direct image on `D⁺` is an isomorphism. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque
    [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))] (f : X ⟶ Y)
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k)))
    [∀ n, TopCat.Sheaf.IsFlasque (K.obj.X n)] :
    IsIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) f).rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨n, hn⟩ := K.property
  obtain ⟨L, _, j, hj⟩ := CochainComplex.Plus.exists_quasiIso_injective K n
  let B := (InjectiveObject.ι (X.Sheaf (ModuleCat.{0} k))).mapCochainComplexPlus.obj L
  have (m : ℤ) : Injective (B.obj.X m) := (L.obj.X m).property
  have (m : ℤ) : TopCat.Sheaf.IsFlasque (B.obj.X m) := isFlasque_of_injective k _
  have : B.obj.IsStrictlyGE n := inferInstanceAs (CochainComplex.IsStrictlyGE
    (((InjectiveObject.ι _).mapHomologicalComplex _).obj L.obj) n)
  have : QuasiIso j.hom := hj
  have hFj := quasiIso_pushforward_of_isFlasque f j.hom n
  have := isIso_Q_map_comp_rightDerivedFunctorPlusUnit
    (TopCat.Sheaf.pushforward (ModuleCat.{0} k) f) (𝟙 _) j hj (by
      rw [Category.id_comp]
      exact hFj)
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using this

/-- **Flasque complexes compute derived global sections**: the case `f = toPt X` of
`isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque`. -/
theorem isIso_rightDerivedFunctorPlusUnit_app_toPt_of_isFlasque
    [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
    (K : CochainComplex.Plus (X.Sheaf (ModuleCat.{0} k)))
    [∀ n, TopCat.Sheaf.IsFlasque (K.obj.X n)] :
    IsIso ((TopCat.Sheaf.pushforward (ModuleCat.{0} k) (toPt X)).rightDerivedFunctorPlusUnit.app
      K) :=
  isIso_rightDerivedFunctorPlusUnit_app_of_isFlasque (toPt X) K

end derived

end TDA.Sheaf
