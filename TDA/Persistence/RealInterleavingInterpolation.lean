import TDA.Persistence.QTame
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Q-tame interpolation from an actual real interleaving

For an `ε`-interleaving, the intermediate module at time `s ∈ [0, ε]` is the
cokernel of the map

`M(t - 2ε + s) × N(t - ε - s) → M(t - s) × N(t - ε + s)`.

The two coordinates of the relation map are the forward maps minus the
interleaving maps.  The resulting quotient is the algebraic interpolation
used in the proof of algebraic stability.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence.RealInterleaving

open CategoryTheory CategoryTheory.Limits RealShift
open scoped NNReal

variable {k : Type u} [Field k] {ε : ℝ≥0}
variable {M N : PModule.{u,0,w} k ℝ}

/-- The order translation used for arbitrary real shifts. -/
private def translateOrder (a : ℝ) : ℝ →o ℝ :=
  ⟨fun t => t + a, fun _ _ h => add_le_add_left h _⟩

/-- Translation of a real persistence module by an arbitrary real amount. -/
private def translate (a : ℝ) (P : PModule.{u,0,w} k ℝ) : PModule.{u,0,w} k ℝ :=
  reindex (translateOrder a) P

@[simp] private theorem translate_obj (a : ℝ) (P : PModule.{u,0,w} k ℝ) (t : ℝ) :
    (translate a P).obj t = P.obj (t + a) := rfl

private def translateMap {P Q : PModule.{u,0,w} k ℝ} (f : P ⟶ Q) (a : ℝ) :
    translate a P ⟶ translate a Q := reindexNatTrans (translateOrder a) f

@[simp] private theorem translateMap_app {P Q : PModule.{u,0,w} k ℝ}
    (f : P ⟶ Q) (a t : ℝ) : (translateMap f a).app t = f.app (t + a) := rfl

private def reindexEqIso {a b : ℝ →o ℝ} (h : ∀ t, a t = b t)
    (P : PModule.{u,0,w} k ℝ) : reindex a P ≅ reindex b P :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun t => eqToIso (h t)) (by intros; apply Subsingleton.elim)) P

@[simp] private theorem reindexEqIso_hom_app {a b : ℝ →o ℝ} (h : ∀ t, a t = b t)
    (P : PModule.{u,0,w} k ℝ) (t : ℝ) :
    (reindexEqIso h P).hom.app t = P.map (eqToHom (h t)) := rfl

private def translateEqIso {a b : ℝ} (h : a = b) (P : PModule.{u,0,w} k ℝ) :
    translate a P ≅ translate b P :=
  reindexEqIso (a := translateOrder a) (b := translateOrder b)
    (fun t => congrArg (fun c : ℝ => t + c) h) P

@[simp] private theorem translateEqIso_hom_app {a b : ℝ} (h : a = b)
    (P : PModule.{u,0,w} k ℝ) (t : ℝ) :
    (translateEqIso h P).hom.app t = P.map (eqToHom (congrArg (fun c : ℝ => t + c) h)) := rfl

@[simp] private theorem translateEqIso_inv_app {a b : ℝ} (h : a = b)
    (P : PModule.{u,0,w} k ℝ) (t : ℝ) :
    (translateEqIso h P).inv.app t =
      P.map (eqToHom (congrArg (fun c : ℝ => t + c) h.symm)) := rfl

private def translateShiftIso (a : ℝ) (P : PModule.{u,0,w} k ℝ) :
    translate a ((shift ε).obj P) ≅ translate (a + (ε : ℝ)) P :=
  reindexEqIso
    (a := (RealShift.translation ε).comp (translateOrder a))
    (b := translateOrder (a + (ε : ℝ)))
    (fun t => by change (t + a) + (ε : ℝ) = t + (a + (ε : ℝ)); ring) P

@[simp] private theorem translateShiftIso_hom_app (a : ℝ)
    (P : PModule.{u,0,w} k ℝ) (t : ℝ) :
    (translateShiftIso a P).hom.app t =
      P.map (eqToHom (show (t + a) + (ε : ℝ) = t + (a + (ε : ℝ)) by ring)) := rfl

private def translateInterleavingMap {P Q : PModule.{u,0,w} k ℝ}
    (f : P ⟶ (shift ε).obj Q) (a b : ℝ) (h : a + (ε : ℝ) = b) :
    translate a P ⟶ translate b Q :=
  translateMap f a ≫ (translateShiftIso a Q).hom ≫ (translateEqIso h Q).hom

@[simp] private theorem translateInterleavingMap_app {P Q : PModule.{u,0,w} k ℝ}
    (f : P ⟶ (shift ε).obj Q) (a b : ℝ) (h : a + (ε : ℝ) = b) (t : ℝ) :
    (translateInterleavingMap f a b h).app t =
      f.app (t + a) ≫ Q.map (eqToHom (show (t + a) + (ε : ℝ) = t + b by
        rw [add_assoc]
        exact congrArg (fun x : ℝ => t + x) h)) := by
  subst b
  simp [translateInterleavingMap, CategoryTheory.NatTrans.comp_app,
    translateMap_app, translateShiftIso_hom_app, translateEqIso_hom_app]

private def pairModule (P Q : PModule.{u,0,w} k ℝ) : PModule.{u,0,w} k ℝ where
  obj t := ModuleCat.of k (P.obj t × Q.obj t)
  map f := ModuleCat.ofHom ((P.map f).hom.prodMap (Q.map f).hom)
  map_id t := by
    apply ModuleCat.hom_ext
    ext x <;> simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x <;> simp [Functor.map_comp]

private theorem pairModule_map_apply {P Q : PModule.{u,0,w} k ℝ}
    {s t : ℝ} (e : s ⟶ t) (x : P.obj s) (y : Q.obj s) :
    ((pairModule P Q).map e).hom (x, y) =
      ((P.map e).hom x, (Q.map e).hom y) := by
  rfl


private def submoduleProdEquiv {V W : Type w} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (S : Submodule k V) (T : Submodule k W) :
    ↥(S.prod T) ≃ₗ[k] ↥S × ↥T where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl

private def pairMap {P Q P' Q' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (g : Q ⟶ P') (h : P ⟶ Q') (j : Q ⟶ Q') :
    pairModule P Q ⟶ pairModule P' Q' := by
  refine ⟨?_, ?_⟩
  · intro t
    exact ModuleCat.ofHom <| LinearMap.prod
      ((f.app t).hom.comp (LinearMap.fst k (P.obj t) (Q.obj t)) +
        (g.app t).hom.comp (LinearMap.snd k (P.obj t) (Q.obj t)))
      ((h.app t).hom.comp (LinearMap.fst k (P.obj t) (Q.obj t)) +
        (j.app t).hom.comp (LinearMap.snd k (P.obj t) (Q.obj t)))
  · intro s t e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hf := congrArg (fun q => q.hom x) (f.naturality e)
    have hg := congrArg (fun q => q.hom y) (g.naturality e)
    have hh := congrArg (fun q => q.hom x) (h.naturality e)
    have hj := congrArg (fun q => q.hom y) (j.naturality e)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hf hg hh hj
    change
      ((f.app t).hom ((P.map e).hom x) +
        (g.app t).hom ((Q.map e).hom y),
       (h.app t).hom ((P.map e).hom x) +
        (j.app t).hom ((Q.map e).hom y)) =
      ((P'.map e).hom ((f.app s).hom x + (g.app s).hom y),
       (Q'.map e).hom ((h.app s).hom x + (j.app s).hom y))
    rw [map_add, map_add, hf, hg, hh, hj]

@[simp] private theorem pairMap_app_apply {P Q P' Q' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (g : Q ⟶ P') (h : P ⟶ Q') (j : Q ⟶ Q') (t : ℝ)
    (x : P.obj t) (y : Q.obj t) :
    ModuleCat.Hom.hom ((pairMap f g h j).app t) (x, y) =
      ((f.app t).hom x + (g.app t).hom y, (h.app t).hom x + (j.app t).hom y) := rfl

private theorem pairMap_ext {P Q P' Q' : PModule.{u,0,w} k ℝ}
    (f f' : P ⟶ P') (g g' : Q ⟶ P') (h h' : P ⟶ Q') (j j' : Q ⟶ Q')
    (hf : f = f') (hg : g = g') (hh : h = h') (hj : j = j') :
    pairMap f g h j = pairMap f' g' h' j' := by
  subst f'
  subst g'
  subst h'
  subst j'
  rfl

private theorem pairMap_diag_comp {P Q P' Q' P'' Q'' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (j : Q ⟶ Q') (f' : P' ⟶ P'') (g' : Q' ⟶ P'')
    (h' : P' ⟶ Q'') (j' : Q' ⟶ Q'') :
    pairMap f 0 0 j ≫ pairMap f' g' h' j' =
      pairMap (f ≫ f') (j ≫ g') (f ≫ h') (j ≫ j') := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairMap_app_apply, zero_add, add_zero]
  change (ModuleCat.Hom.hom ((pairMap f' g' h' j').app t))
      ((ModuleCat.Hom.hom ((pairMap f 0 0 j).app t)) (x, y)) = _
  simp [pairMap_app_apply, NatTrans.app_zero, map_add]
  rfl

private theorem pairMap_comp_diag {P Q P' Q' P'' Q'' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (g : Q ⟶ P') (h : P ⟶ Q') (j : Q ⟶ Q')
    (f' : P' ⟶ P'') (j' : Q' ⟶ Q'') :
    pairMap f g h j ≫ pairMap f' 0 0 j' =
      pairMap (f ≫ f') (g ≫ f') (h ≫ j') (j ≫ j') := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairMap_app_apply]
  change (ModuleCat.Hom.hom ((pairMap f' 0 0 j').app t))
      ((ModuleCat.Hom.hom ((pairMap f g h j).app t)) (x, y)) = _
  simp [pairMap_app_apply, map_add]
  rfl

private theorem pairMap_diag_transition (P Q : PModule.{u,0,w} k ℝ)
    (d : ℝ≥0) :
    pairMap (RealShift.transition d P) 0 0 (RealShift.transition d Q) =
      RealShift.transition d (pairModule P Q) := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  rw [pairMap_app_apply]
  simp only [NatTrans.app_zero, ModuleCat.hom_zero, map_zero,
    LinearMap.zero_apply, zero_add, add_zero]
  simp only [RealShift.transition_app, structureMap]
  change ((P.map (homOfLE (le_add_of_nonneg_right d.coe_nonneg))).hom x,
      (Q.map (homOfLE (le_add_of_nonneg_right d.coe_nonneg))).hom y) =
    ((pairModule P Q).map (homOfLE (le_add_of_nonneg_right d.coe_nonneg))).hom (x, y)
  rw [pairModule_map_apply]

private def pairDescMap {P Q R : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) : pairModule P Q ⟶ R where
  app t := ModuleCat.ofHom
    ((f.app t).hom.comp (LinearMap.fst k (P.obj t) (Q.obj t)) +
      (g.app t).hom.comp (LinearMap.snd k (P.obj t) (Q.obj t)))
  naturality a b e := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    have hf := congrArg (fun q => q.hom x) (f.naturality e)
    have hg := congrArg (fun q => q.hom y) (g.naturality e)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hf hg
    change (f.app b).hom ((P.map e).hom x) +
        (g.app b).hom ((Q.map e).hom y) =
      (R.map e).hom ((f.app a).hom x + (g.app a).hom y)
    rw [map_add, hf, hg]

@[simp] private theorem pairDescMap_app_apply {P Q R : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) (t : ℝ) (x : P.obj t) (y : Q.obj t) :
    ((pairDescMap f g).app t).hom (x, y) =
      (f.app t).hom x + (g.app t).hom y := rfl

private def pairInl {P Q : PModule.{u,0,w} k ℝ} : P ⟶ pairModule P Q := by
  refine ⟨?_, ?_⟩
  · intro t
    exact ModuleCat.ofHom (LinearMap.inl k (P.obj t) (Q.obj t))
  · intro s t e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((P.map e).hom x, 0) = ((P.map e).hom x, (Q.map e).hom 0)
    simp

private def pairInr {P Q : PModule.{u,0,w} k ℝ} : Q ⟶ pairModule P Q := by
  refine ⟨?_, ?_⟩
  · intro t
    exact ModuleCat.ofHom (LinearMap.inr k (P.obj t) (Q.obj t))
  · intro s t e
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (0, (Q.map e).hom x) = ((P.map e).hom 0, (Q.map e).hom x)
    simp

@[simp] private theorem pairInl_app_apply {P Q : PModule.{u,0,w} k ℝ} (t : ℝ)
    (x : P.obj t) : (pairInl (P := P) (Q := Q)).app t x = (x, 0) := rfl

@[simp] private theorem pairInr_app_apply {P Q : PModule.{u,0,w} k ℝ} (t : ℝ)
    (y : Q.obj t) : (pairInr (P := P) (Q := Q)).app t y = (0, y) := rfl

@[simp] private theorem pairInr_pairMap_app_apply
    {P Q P' Q' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (g : Q ⟶ P') (h : P ⟶ Q') (j : Q ⟶ Q')
    (t : ℝ) (y : Q.obj t) :
    ((pairInr ≫ pairMap f g h j).app t).hom y =
      ((g.app t).hom y, (j.app t).hom y) := by
  simp [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

private theorem pairInr_comp_pairMap {P Q P' Q' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (g : Q ⟶ P') (h : P ⟶ Q') (j : Q ⟶ Q') :
    pairInr ≫ pairMap f g h j = g ≫ pairInl + j ≫ pairInr := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  simp [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairInr_pairMap_app_apply, pairInl_app_apply, pairInr_app_apply,
    NatTrans.app_add, ModuleCat.hom_add]
  change ((g.app t).hom y, (j.app t).hom y) =
    ((g.app t).hom y, 0) + (0, (j.app t).hom y)
  ext
  · change (g.app t).hom y = (g.app t).hom y + 0
    simp
  · change (j.app t).hom y = 0 + (j.app t).hom y
    simp

private theorem pairInl_comp_pairMap {P Q P' Q' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (g : Q ⟶ P') (h : P ⟶ Q') (j : Q ⟶ Q') :
    pairInl ≫ pairMap f g h j = f ≫ pairInl + h ≫ pairInr := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairInl_app_apply, pairInr_app_apply, NatTrans.app_add, ModuleCat.hom_add]
  change ((f.app t).hom x, (h.app t).hom x) =
    ((f.app t).hom x, 0) + (0, (h.app t).hom x)
  ext
  · change (f.app t).hom x = (f.app t).hom x + 0
    simp
  · change (h.app t).hom x = 0 + (h.app t).hom x
    simp

private theorem pairInl_pairDescMap {P Q R : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) : pairInl ≫ pairDescMap f g = f := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairInl_app_apply, pairDescMap_app_apply, map_zero, add_zero]

private theorem pairInr_pairDescMap {P Q R : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) : pairInr ≫ pairDescMap f g = g := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairInr_app_apply, pairDescMap_app_apply, map_zero, zero_add]

private theorem pairInl_pairDescMap_comp {P Q R S : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) (h : R ⟶ S) :
    pairInl ≫ (pairDescMap f g ≫ h) = f ≫ h := by
  rw [← Category.assoc pairInl, pairInl_pairDescMap]

private theorem pairInr_pairDescMap_comp {P Q R S : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) (h : R ⟶ S) :
    pairInr ≫ (pairDescMap f g ≫ h) = g ≫ h := by
  rw [← Category.assoc pairInr, pairInr_pairDescMap]

private theorem pairInl_pairDescMap_comp_comp
    {P Q R S T : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) (h : R ⟶ S) (j : S ⟶ T) :
    pairInl ≫ ((pairDescMap f g ≫ h) ≫ j) = (f ≫ h) ≫ j := by
  rw [← Category.assoc, ← Category.assoc pairInl, pairInl_pairDescMap]

private theorem pairInr_pairDescMap_comp_comp
    {P Q R S T : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) (h : R ⟶ S) (j : S ⟶ T) :
    pairInr ≫ ((pairDescMap f g ≫ h) ≫ j) = (g ≫ h) ≫ j := by
  rw [← Category.assoc, ← Category.assoc pairInr, pairInr_pairDescMap]

private theorem pairModule_hom_ext {P Q R : PModule.{u,0,w} k ℝ}
    (f g : pairModule P Q ⟶ R)
    (hinl : pairInl ≫ f = pairInl ≫ g)
    (hinr : pairInr ≫ f = pairInr ≫ g) : f = g := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have h1 := congrArg (fun q => (q.app t).hom x) hinl
  have h2 := congrArg (fun q => (q.app t).hom y) hinr
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairInl_app_apply] at h1
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    pairInr_app_apply] at h2
  have hp : (x, y) = (x, 0) + (0, y) := by ext <;> simp
  change (f.app t).hom (x, y) = (g.app t).hom (x, y)
  have hpf := congrArg (fun z : P.obj t × Q.obj t => (f.app t).hom z) hp
  have hpg := congrArg (fun z : P.obj t × Q.obj t => (g.app t).hom z) hp
  calc
    (f.app t).hom (x, y) = (f.app t).hom ((x, 0) + (0, y)) := hpf
    _ = (f.app t).hom (x, 0) + (f.app t).hom (0, y) :=
      map_add (f.app t).hom (x, 0) (0, y)
    _ = (g.app t).hom (x, 0) + (g.app t).hom (0, y) := by rw [h1, h2]
    _ = (g.app t).hom ((x, 0) + (0, y)) :=
      (map_add (g.app t).hom (x, 0) (0, y)).symm
    _ = (g.app t).hom (x, y) := hpg.symm

private theorem compIso_pairModule_hom (P Q : PModule.{u,0,w} k ℝ)
    (d : ℝ≥0) :
    (RealShift.compIso d d (pairModule P Q)).hom =
      pairMap (RealShift.compIso d d P).hom 0 0
        (RealShift.compIso d d Q).hom := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change ((shift d).obj ((shift d).obj P)).obj t at x
  change ((shift d).obj ((shift d).obj Q)).obj t at y
  conv_lhs => rw [RealShift.compIso_hom_app d d (pairModule P Q) t]
  have hpm := pairMap_app_apply (f := (RealShift.compIso d d P).hom)
    (g := 0) (h := 0) (j := (RealShift.compIso d d Q).hom) t x y
  conv_rhs => erw [hpm]
  simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, zero_add, add_zero]
  change ((P.map (eqToHom (show (t + (d : ℝ)) + (d : ℝ) =
      t + ((d + d : ℝ≥0) : ℝ) by simp [add_assoc]))).hom x,
      (Q.map (eqToHom (show (t + (d : ℝ)) + (d : ℝ) =
      t + ((d + d : ℝ≥0) : ℝ) by simp [add_assoc]))).hom y) =
    (((RealShift.compIso d d P).hom.app t).hom x,
      ((RealShift.compIso d d Q).hom.app t).hom y)
  rw [RealShift.compIso_hom_app, RealShift.compIso_hom_app]
  rfl

private theorem pairMap_comp_pairDescMap_zero {P Q R S : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) (h : P ⟶ S) (j : Q ⟶ S) (a : S ⟶ R)
    (hf : h ≫ a = -f) (hg : j ≫ a = -g) :
    pairMap f g h j ≫ pairDescMap (𝟙 R) a = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hx := congrArg (fun q => (q.app t).hom x) hf
  have hy := congrArg (fun q => (q.app t).hom y) hg
  change (a.app t).hom ((h.app t).hom x) = -((f.app t).hom x) at hx
  change (a.app t).hom ((j.app t).hom y) = -((g.app t).hom y) at hy
  change (f.app t).hom x + (g.app t).hom y +
    (a.app t).hom ((h.app t).hom x + (j.app t).hom y) = 0
  rw [map_add, hx, hy]
  abel

private theorem pairMap_comp_pairDescMap_zero_general
    {P Q R S T : PModule.{u,0,w} k ℝ}
    (f : P ⟶ R) (g : Q ⟶ R) (h : P ⟶ S) (j : Q ⟶ S)
    (a : R ⟶ T) (b : S ⟶ T)
    (hf : f ≫ a = -(h ≫ b)) (hg : g ≫ a = -(j ≫ b)) :
    pairMap f g h j ≫ pairDescMap a b = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hx := congrArg (fun q => (q.app t).hom x) hf
  have hy := congrArg (fun q => (q.app t).hom y) hg
  change (a.app t).hom ((f.app t).hom x) =
    -((b.app t).hom ((h.app t).hom x)) at hx
  change (a.app t).hom ((g.app t).hom y) =
    -((b.app t).hom ((j.app t).hom y)) at hy
  change (a.app t).hom ((f.app t).hom x + (g.app t).hom y) +
      (b.app t).hom ((h.app t).hom x + (j.app t).hom y) = 0
  rw [map_add, map_add, hx, hy]
  abel

private def translateStructure (P : PModule.{u,0,w} k ℝ) (a b : ℝ) (hab : a ≤ b) :
    translate a P ⟶ translate b P where
  app t := structureMap P (add_le_add_right hab t)
  naturality s t f := by
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1

private def translateToShiftStructure (P : PModule.{u,0,w} k ℝ)
    (a b : ℝ) (d : ℝ≥0) (hab : a ≤ (d : ℝ) + b) :
    translate a P ⟶ (shift d).obj (translate b P) where
  app t := structureMap P (by
    calc
      t + a ≤ t + ((d : ℝ) + b) := by
        simpa [add_comm] using add_le_add_left hab t
      _ = (t + (d : ℝ)) + b := by ring)
  naturality s t e := by
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1

private theorem translateToShiftStructure_self_transition
    (P : PModule.{u,0,w} k ℝ) (a : ℝ) (d : ℝ≥0)
    (ha : a ≤ (d : ℝ) + a) :
    translateToShiftStructure P a a d ha = RealShift.transition d (translate a P) := by
  apply NatTrans.ext
  funext t
  dsimp only [translateToShiftStructure, RealShift.transition_app,
    structureMap, translate_obj, translateOrder]
  congr 1

private theorem translateInterleavingMap_shift_naturality
    {P Q : PModule.{u,0,w} k ℝ} (f : P ⟶ (shift ε).obj Q)
    (a a' b b' : ℝ) (d : ℝ≥0)
    (hab : a + (ε : ℝ) = b) (ha'b' : a' + (ε : ℝ) = b')
    (hA : a ≤ (d : ℝ) + a') (hB : b ≤ (d : ℝ) + b') :
    translateInterleavingMap f a b hab ≫
        translateToShiftStructure Q b b' d hB =
      translateToShiftStructure P a a' d hA ≫
        (shift d).map (translateInterleavingMap f a' b' ha'b') := by
  apply NatTrans.ext
  funext t
  simp only [NatTrans.comp_app, translateInterleavingMap_app,
    translateToShiftStructure, RealShift.shift_map_app, RealShift.shift_obj,
    RealShift.translation_apply]
  let eA : (t + a) ⟶ ((t + (d : ℝ)) + a') :=
    homOfLE (by
      calc
        t + a ≤ t + ((d : ℝ) + a') := by
          simpa [add_comm] using add_le_add_left hA t
        _ = (t + (d : ℝ)) + a' := by ring)
  have hn := f.naturality eA
  change P.map eA ≫ f.app ((t + (d : ℝ)) + a') =
    f.app (t + a) ≫ Q.map ((translation ε).toFunctor.map eA) at hn
  let e1 : (RealShift.translation ε).toFunctor.obj (t + a) ⟶ t + b :=
    eqToHom (by
      change (t + a) + (ε : ℝ) = t + b
      rw [add_assoc, hab])
  let eB : t + b ⟶ (t + (d : ℝ)) + b' := homOfLE (by
    calc
      t + b ≤ t + ((d : ℝ) + b') := by
        simpa [add_comm] using add_le_add_left hB t
      _ = (t + (d : ℝ)) + b' := by ring)
  let e2 : (RealShift.translation ε).toFunctor.obj
      ((t + (d : ℝ)) + a') ⟶ (t + (d : ℝ)) + b' :=
    eqToHom (by
      change ((t + (d : ℝ)) + a') + (ε : ℝ) = (t + (d : ℝ)) + b'
      rw [add_assoc, ha'b'])
  have hpath : e1 ≫ eB = ((translation ε).toFunctor.map eA) ≫ e2 := by
    apply Subsingleton.elim
  let f0 : P.obj (t + a) ⟶ Q.obj ((RealShift.translation ε).toFunctor.obj (t + a)) :=
    f.app (t + a)
  let f1 : P.obj ((t + (d : ℝ)) + a') ⟶
      Q.obj ((RealShift.translation ε).toFunctor.obj ((t + (d : ℝ)) + a')) :=
    f.app ((t + (d : ℝ)) + a')
  have hn' := hn
  change P.map eA ≫ f1 = f0 ≫ Q.map ((translation ε).toFunctor.map eA) at hn'
  dsimp only [structureMap]
  change (f0 ≫ Q.map e1) ≫ Q.map eB =
    (P.map eA ≫ f1) ≫ Q.map e2
  calc
    (f0 ≫ Q.map e1) ≫ Q.map eB =
        f0 ≫ (Q.map e1 ≫ Q.map eB) := by
          exact Category.assoc _ _ _
    _ = f0 ≫ Q.map (e1 ≫ eB) := by
          rw [← Q.map_comp]
    _ = f0 ≫ Q.map (((translation ε).toFunctor.map eA) ≫ e2) := by
          rw [hpath]
    _ = f0 ≫
        (Q.map ((translation ε).toFunctor.map eA) ≫ Q.map e2) := by
          rw [Q.map_comp]
    _ = (f0 ≫ Q.map ((translation ε).toFunctor.map eA)) ≫ Q.map e2 := by
          exact (Category.assoc _ _ _).symm
    _ = (P.map eA ≫ f1) ≫ Q.map e2 := by
          rw [← hn']

private theorem translateStructure_comp (P : PModule.{u,0,w} k ℝ)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    translateStructure P a b hab ≫ translateStructure P b c hbc =
      translateStructure P a c (hab.trans hbc) := by
  apply NatTrans.ext
  funext t
  change structureMap P (add_le_add_right hab t) ≫
      structureMap P (add_le_add_right hbc t) =
    structureMap P (add_le_add_right (hab.trans hbc) t)
  exact structureMap_comp P _ _

private theorem translateStructure_shift_naturality
    (P : PModule.{u,0,w} k ℝ) (a a' b b' : ℝ) (d : ℝ≥0)
    (hab : a ≤ b) (ha'b' : a' ≤ b')
    (hA : a ≤ (d : ℝ) + a') (hB : b ≤ (d : ℝ) + b') :
    translateToShiftStructure P a a' d hA ≫
        (shift d).map (translateStructure P a' b' ha'b') =
      translateStructure P a b hab ≫
        translateToShiftStructure P b b' d hB := by
  apply NatTrans.ext
  funext t
  dsimp only [translateToShiftStructure, translateStructure,
    RealShift.shift_map_app, RealShift.shift_obj, translate_obj]
  change structureMap P _ ≫ structureMap P _ =
    structureMap P _ ≫ structureMap P _
  erw [structureMap_comp, structureMap_comp]

private theorem translateToShiftStructure_comp_compIso
    (P : PModule.{u,0,w} k ℝ) (a b c : ℝ) (d : ℝ≥0)
    (hab : a ≤ (d : ℝ) + b) (hbc : b ≤ (d : ℝ) + c)
    (hac : a ≤ ((d + d : ℝ≥0) : ℝ) + c) :
    translateToShiftStructure P a b d hab ≫
        (shift d).map (translateToShiftStructure P b c d hbc) ≫
        (RealShift.compIso d d (translate c P)).hom =
      translateToShiftStructure P a c (d + d) hac := by
  apply NatTrans.ext
  funext t
  simp only [NatTrans.comp_app, translateToShiftStructure,
    RealShift.shift_map_app, RealShift.compIso_hom_app]
  change P.map _ ≫ P.map _ ≫ P.map _ = P.map _
  erw [← P.map_comp, ← P.map_comp]
  congr 1

private theorem shift_pairMap {P Q P' Q' : PModule.{u,0,w} k ℝ}
    (f : P ⟶ P') (g : Q ⟶ P') (h : P ⟶ Q') (j : Q ⟶ Q') (d : ℝ≥0) :
    (shift d).map (pairMap f g h j) =
      pairMap ((shift d).map f) ((shift d).map g)
        ((shift d).map h) ((shift d).map j) := by
  rfl

private theorem shift_pairModule_obj (P Q : PModule.{u,0,w} k ℝ) (d : ℝ≥0) :
    (shift d).obj (pairModule P Q) =
      pairModule ((shift d).obj P) ((shift d).obj Q) := by
  rfl

private theorem shift_map_neg {P Q : PModule.{u,0,w} k ℝ}
    (f : P ⟶ Q) (d : ℝ≥0) :
    (shift d).map (-f) = -(shift d).map f := by
  apply NatTrans.ext
  funext t
  simp [RealShift.shift_map_app]
  rfl

private theorem shift_map_zero {P Q : PModule.{u,0,w} k ℝ} (d : ℝ≥0) :
    (shift d).map (0 : P ⟶ Q) = 0 := by
  apply NatTrans.ext
  funext t
  simp [RealShift.shift_map_app]
  rfl

private theorem translateEqIso_inv_comp_translateStructure
    (P : PModule.{u,0,w} k ℝ) (a b : ℝ) (h : a = b) (hab : a ≤ b) :
    (translateEqIso h P).inv ≫ translateStructure P a b hab =
      𝟙 (translate b P) := by
  subst b
  apply NatTrans.ext
  funext t
  simp [NatTrans.comp_app, translateEqIso_inv_app, translateStructure,
    translate_obj, translateOrder]
  rfl

private theorem translateInterleavingMap_comp (i : RealInterleaving ε M N)
    (a b c : ℝ) (hab : a + (ε : ℝ) = b) (hbc : b + (ε : ℝ) = c)
    (hac : a ≤ c) :
    translateInterleavingMap i.φ a b hab ≫ translateInterleavingMap i.ψ b c hbc =
      translateStructure M a c hac := by
  apply NatTrans.ext
  funext t
  simp only [NatTrans.comp_app, translateInterleavingMap_app]
  let e : (t + a) + (ε : ℝ) ⟶ t + b := eqToHom (by rw [add_assoc, hab])
  have hn := i.ψ.naturality e
  change N.map e ≫ i.ψ.app (t + b) =
    i.ψ.app ((t + a) + (ε : ℝ)) ≫ M.map ((translation ε).toFunctor.map e) at hn
  change (i.φ.app (t + a) ≫ N.map e) ≫
      (i.ψ.app (t + b) ≫ M.map _) = M.map _
  erw [Category.assoc, ← Category.assoc (N.map e), hn]
  erw [Category.assoc,
    ← Category.assoc (i.φ.app (t + a)) (i.ψ.app ((t + a) + (ε : ℝ))),
    i.φ_ψ_structureMap]
  unfold structureMap
  erw [← M.map_comp, ← M.map_comp]
  congr 1

private theorem translateInterleavingMap_ψφ_comp (i : RealInterleaving ε M N)
    (a b c : ℝ) (hab : a + (ε : ℝ) = b) (hbc : b + (ε : ℝ) = c)
    (hac : a ≤ c) :
    translateInterleavingMap i.ψ a b hab ≫ translateInterleavingMap i.φ b c hbc =
      translateStructure N a c hac := by
  apply NatTrans.ext
  funext t
  simp only [NatTrans.comp_app, translateInterleavingMap_app]
  let e : (t + a) + (ε : ℝ) ⟶ t + b := eqToHom (by rw [add_assoc, hab])
  have hn := i.φ.naturality e
  change M.map e ≫ i.φ.app (t + b) =
    i.φ.app ((t + a) + (ε : ℝ)) ≫ N.map ((translation ε).toFunctor.map e) at hn
  change (i.ψ.app (t + a) ≫ M.map e) ≫
      (i.φ.app (t + b) ≫ N.map _) = N.map _
  erw [Category.assoc, ← Category.assoc (M.map e), hn]
  erw [Category.assoc,
    ← Category.assoc (i.ψ.app (t + a)) (i.φ.app ((t + a) + (ε : ℝ))),
    i.symm.φ_ψ_structureMap]
  unfold structureMap
  erw [← N.map_comp, ← N.map_comp]
  congr 1

private theorem translateEqIso_inv_comp_interleavingMap
    {P Q : PModule.{u,0,w} k ℝ} (f : P ⟶ (shift ε).obj Q)
    (a b c : ℝ) (hab : a + (ε : ℝ) = c) (hbc : b + (ε : ℝ) = c)
    (h : a = b) :
    (translateEqIso h P).inv ≫ translateInterleavingMap f a c hab =
      translateInterleavingMap f b c hbc := by
  subst b
  apply NatTrans.ext
  funext t
  simp [translateEqIso_inv_app, translateInterleavingMap_app]

private theorem translateStructure_comp_interleavingMap
    {P Q : PModule.{u,0,w} k ℝ} (f : P ⟶ (shift ε).obj Q)
    (a b c : ℝ) (hab : a ≤ b)
    (hbc : b + (ε : ℝ) = c) (hac : a + (ε : ℝ) = c) :
    translateStructure P a b hab ≫ translateInterleavingMap f b c hbc =
      translateInterleavingMap f a c hac := by
  apply NatTrans.ext
  funext t
  simp only [NatTrans.comp_app, translateInterleavingMap_app]
  let e : t + a ⟶ t + b := homOfLE (add_le_add_right hab t)
  have hn := f.naturality e
  change P.map e ≫ f.app (t + b) =
    f.app (t + a) ≫ Q.map ((translation ε).toFunctor.map e) at hn
  change P.map e ≫ (f.app (t + b) ≫ Q.map _) = f.app (t + a) ≫ Q.map _
  erw [← Category.assoc, hn, Category.assoc, ← Q.map_comp]
  congr 1

/-- The intermediate parameters, with both endpoints included. -/
abbrev InterpolationTime (ε : ℝ≥0) := {s : ℝ // 0 ≤ s ∧ s ≤ (ε : ℝ)}

private abbrev interpolationSource (s : InterpolationTime ε) :
    PModule.{u,0,w} k ℝ :=
  pairModule (translate (s.1 - 2 * (ε : ℝ)) M)
    (translate (-(ε : ℝ) - s.1) N)

private abbrev interpolationTarget (s : InterpolationTime ε) :
    PModule.{u,0,w} k ℝ :=
  pairModule (translate (-s.1) M) (translate (s.1 - (ε : ℝ)) N)

private def interpolationDelta (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) : ℝ≥0 :=
  ⟨r.1 - s.1, sub_nonneg.mpr hsr⟩

private theorem interpolationDelta_eq_nndist (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) : interpolationDelta s r hsr = nndist s.1 r.1 := by
  apply NNReal.coe_injective
  change r.1 - s.1 = dist s.1 r.1
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hsr)]
  ring

private def interpolationTargetForward (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolationTarget (k := k) (M := M) (N := N) s ⟶
      (shift (interpolationDelta s r hsr)).obj
        (interpolationTarget (k := k) (M := M) (N := N) r) := by
  let d := interpolationDelta s r hsr
  exact pairMap
    (translateToShiftStructure M (-s.1) (-r.1) d (by
      rw [show (d : ℝ) = r.1 - s.1 by rfl]
      linarith))
    0 0
    (translateToShiftStructure N (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ)) d (by
      rw [show (d : ℝ) = r.1 - s.1 by rfl]
      linarith))

private def interpolationSourceForward (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolationSource (k := k) (M := M) (N := N) s ⟶
      (shift (interpolationDelta s r hsr)).obj
        (interpolationSource (k := k) (M := M) (N := N) r) := by
  let d := interpolationDelta s r hsr
  exact pairMap
    (translateToShiftStructure M (s.1 - 2 * (ε : ℝ))
      (r.1 - 2 * (ε : ℝ)) d (by
        rw [show (d : ℝ) = r.1 - s.1 by rfl]
        linarith))
    0 0
    (translateToShiftStructure N (-(ε : ℝ) - s.1)
      (-(ε : ℝ) - r.1) d (by
        rw [show (d : ℝ) = r.1 - s.1 by rfl]
        linarith))

private def interpolationTargetBackward (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolationTarget (k := k) (M := M) (N := N) r ⟶
      (shift (interpolationDelta s r hsr)).obj
        (interpolationTarget (k := k) (M := M) (N := N) s) := by
  let d := interpolationDelta s r hsr
  exact pairMap
    (translateToShiftStructure M (-r.1) (-s.1) d (by
      rw [show (d : ℝ) = r.1 - s.1 by rfl]
      linarith))
    0 0
    (translateToShiftStructure N (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ)) d (by
      rw [show (d : ℝ) = r.1 - s.1 by rfl]
      linarith))

private def interpolationSourceBackward (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolationSource (k := k) (M := M) (N := N) r ⟶
      (shift (interpolationDelta s r hsr)).obj
        (interpolationSource (k := k) (M := M) (N := N) s) := by
  let d := interpolationDelta s r hsr
  exact pairMap
    (translateToShiftStructure M (r.1 - 2 * (ε : ℝ))
      (s.1 - 2 * (ε : ℝ)) d (by
        rw [show (d : ℝ) = r.1 - s.1 by rfl]
        linarith))
    0 0
    (translateToShiftStructure N (-(ε : ℝ) - r.1)
      (-(ε : ℝ) - s.1) d (by
        rw [show (d : ℝ) = r.1 - s.1 by rfl]
        linarith))

private theorem interpolationTarget_forward_backward_comp
    (s r : InterpolationTime ε) (hsr : s.1 ≤ r.1) :
    interpolationTargetForward (k := k) (M := M) (N := N) s r hsr ≫
        (shift (interpolationDelta s r hsr)).map
          (interpolationTargetBackward (k := k) (M := M) (N := N) s r hsr) ≫
        (RealShift.compIso (interpolationDelta s r hsr)
          (interpolationDelta s r hsr) (interpolationTarget s)).hom =
      RealShift.transition (interpolationDelta s r hsr + interpolationDelta s r hsr)
        (interpolationTarget s) := by
  unfold interpolationTargetForward interpolationTargetBackward
  dsimp only [interpolationTarget]
  erw [shift_pairMap, shift_map_zero, shift_map_zero]
  change pairMap (translateToShiftStructure M (-s.1) (-r.1)
      (interpolationDelta s r hsr) _) 0 0
      (translateToShiftStructure N (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ))
        (interpolationDelta s r hsr) _) ≫
    pairMap ((shift (interpolationDelta s r hsr)).map
      (translateToShiftStructure M (-r.1) (-s.1) (interpolationDelta s r hsr) _)) 0 0
      ((shift (interpolationDelta s r hsr)).map
        (translateToShiftStructure N (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ))
          (interpolationDelta s r hsr) _)) ≫
    (RealShift.compIso (interpolationDelta s r hsr)
      (interpolationDelta s r hsr)
      (pairModule (translate (-s.1) M) (translate (s.1 - (ε : ℝ)) N))).hom =
      RealShift.transition (interpolationDelta s r hsr + interpolationDelta s r hsr)
        (pairModule (translate (-s.1) M) (translate (s.1 - (ε : ℝ)) N))
  erw [compIso_pairModule_hom]
  let d := interpolationDelta s r hsr
  let f := translateToShiftStructure M (-s.1) (-r.1) d (by
    rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
  let j := translateToShiftStructure N (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ)) d (by
    rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
  let fb := (shift d).map (translateToShiftStructure M (-r.1) (-s.1) d (by
    rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith))
  let jb := (shift d).map (translateToShiftStructure N (r.1 - (ε : ℝ))
    (s.1 - (ε : ℝ)) d (by
      rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith))
  let cm := (RealShift.compIso d d (translate (-s.1) M)).hom
  let cn := (RealShift.compIso d d (translate (s.1 - (ε : ℝ)) N)).hom
  change pairMap f 0 0 j ≫ pairMap fb 0 0 jb ≫ pairMap cm 0 0 cn =
    RealShift.transition (d + d) (pairModule (translate (-s.1) M)
      (translate (s.1 - (ε : ℝ)) N))
  have hfirst := pairMap_diag_comp
    (f := f) (j := j) (f' := fb)
    (g' := 0) (h' := 0)
    (j' := jb)
  have hsecond := pairMap_diag_comp
    (f := f ≫ fb) (j := j ≫ jb) (f' := cm)
    (g' := 0) (h' := 0)
    (j' := cn)
  have hmatrix :
      pairMap f 0 0 j ≫ pairMap fb 0 0 jb ≫ pairMap cm 0 0 cn =
        pairMap (RealShift.transition (d + d) (translate (-s.1) M)) 0 0
          (RealShift.transition (d + d) (translate (s.1 - (ε : ℝ)) N)) := by
    calc
      _ = (pairMap f 0 0 j ≫ pairMap fb 0 0 jb) ≫ pairMap cm 0 0 cn :=
        (Category.assoc _ _ _).symm
      _ = (pairMap (f ≫ fb) 0 0 (j ≫ jb)) ≫ pairMap cm 0 0 cn := by
        calc
          _ = (pairMap (f ≫ fb) (j ≫ (0 : _)) (f ≫ (0 : _)) (j ≫ jb)) ≫
              pairMap cm 0 0 cn := congrArg (fun x => x ≫ pairMap cm 0 0 cn) hfirst
          _ = (pairMap (f ≫ fb) 0 0 (j ≫ jb)) ≫ pairMap cm 0 0 cn := by
            simp only [comp_zero]
      _ = pairMap ((f ≫ fb) ≫ cm) 0 0 ((j ≫ jb) ≫ cn) := by
        rw [hsecond]
        simp only [comp_zero]
      _ = pairMap (RealShift.transition (d + d) (translate (-s.1) M)) 0 0
          (RealShift.transition (d + d) (translate (s.1 - (ε : ℝ)) N)) := by
        apply pairMap_ext
        · calc
            _ = translateToShiftStructure M (-s.1) (-s.1) (d + d) (by
              simp only [NNReal.coe_add]
              linarith [d.coe_nonneg]) :=
              translateToShiftStructure_comp_compIso M (-s.1) (-r.1) (-s.1) d
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by simp only [NNReal.coe_add]; linarith [d.coe_nonneg])
            _ = RealShift.transition (d + d) (translate (-s.1) M) :=
              translateToShiftStructure_self_transition M (-s.1) _ (by
                simp only [NNReal.coe_add]
                linarith [d.coe_nonneg])
        · simp
        · simp
        · calc
            _ = translateToShiftStructure N (s.1 - (ε : ℝ)) (s.1 - (ε : ℝ))
                (d + d) (by
                  simp only [NNReal.coe_add]
                  linarith [d.coe_nonneg]) :=
              translateToShiftStructure_comp_compIso N (s.1 - (ε : ℝ))
                (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ)) d
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by simp only [NNReal.coe_add]; linarith [d.coe_nonneg])
            _ = RealShift.transition (d + d) (translate (s.1 - (ε : ℝ)) N) :=
              translateToShiftStructure_self_transition N (s.1 - (ε : ℝ)) _
                (by simp only [NNReal.coe_add]; linarith [d.coe_nonneg])
  have hdiag := pairMap_diag_transition (translate (-s.1) M)
    (translate (s.1 - (ε : ℝ)) N) (d + d)
  exact hmatrix.trans hdiag

private theorem interpolationTarget_backward_forward_comp
    (s r : InterpolationTime ε) (hsr : s.1 ≤ r.1) :
    interpolationTargetBackward (k := k) (M := M) (N := N) s r hsr ≫
        (shift (interpolationDelta s r hsr)).map
          (interpolationTargetForward (k := k) (M := M) (N := N) s r hsr) ≫
        (RealShift.compIso (interpolationDelta s r hsr)
          (interpolationDelta s r hsr) (interpolationTarget r)).hom =
      RealShift.transition (interpolationDelta s r hsr + interpolationDelta s r hsr)
        (interpolationTarget r) := by
  unfold interpolationTargetBackward interpolationTargetForward
  dsimp only [interpolationTarget]
  erw [shift_pairMap, shift_map_zero, shift_map_zero]
  change pairMap (translateToShiftStructure M (-r.1) (-s.1)
      (interpolationDelta s r hsr) _) 0 0
      (translateToShiftStructure N (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ))
        (interpolationDelta s r hsr) _) ≫
    pairMap ((shift (interpolationDelta s r hsr)).map
      (translateToShiftStructure M (-s.1) (-r.1) (interpolationDelta s r hsr) _)) 0 0
      ((shift (interpolationDelta s r hsr)).map
        (translateToShiftStructure N (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ))
          (interpolationDelta s r hsr) _)) ≫
    (RealShift.compIso (interpolationDelta s r hsr)
      (interpolationDelta s r hsr)
      (pairModule (translate (-r.1) M) (translate (r.1 - (ε : ℝ)) N))).hom =
      RealShift.transition (interpolationDelta s r hsr + interpolationDelta s r hsr)
        (pairModule (translate (-r.1) M) (translate (r.1 - (ε : ℝ)) N))
  erw [compIso_pairModule_hom]
  let d := interpolationDelta s r hsr
  let f := translateToShiftStructure M (-r.1) (-s.1) d (by
    rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
  let j := translateToShiftStructure N (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ)) d (by
    rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
  let fb := (shift d).map (translateToShiftStructure M (-s.1) (-r.1) d (by
    rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith))
  let jb := (shift d).map (translateToShiftStructure N (s.1 - (ε : ℝ))
    (r.1 - (ε : ℝ)) d (by
      rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith))
  let cm := (RealShift.compIso d d (translate (-r.1) M)).hom
  let cn := (RealShift.compIso d d (translate (r.1 - (ε : ℝ)) N)).hom
  change pairMap f 0 0 j ≫ pairMap fb 0 0 jb ≫ pairMap cm 0 0 cn =
    RealShift.transition (d + d) (pairModule (translate (-r.1) M)
      (translate (r.1 - (ε : ℝ)) N))
  have hfirst := pairMap_diag_comp (f := f) (j := j) (f' := fb)
    (g' := 0) (h' := 0) (j' := jb)
  have hsecond := pairMap_diag_comp (f := f ≫ fb) (j := j ≫ jb) (f' := cm)
    (g' := 0) (h' := 0) (j' := cn)
  have hmatrix :
      pairMap f 0 0 j ≫ pairMap fb 0 0 jb ≫ pairMap cm 0 0 cn =
        pairMap (RealShift.transition (d + d) (translate (-r.1) M)) 0 0
          (RealShift.transition (d + d) (translate (r.1 - (ε : ℝ)) N)) := by
    calc
      _ = (pairMap f 0 0 j ≫ pairMap fb 0 0 jb) ≫ pairMap cm 0 0 cn :=
        (Category.assoc _ _ _).symm
      _ = (pairMap (f ≫ fb) 0 0 (j ≫ jb)) ≫ pairMap cm 0 0 cn := by
        calc
          _ = (pairMap (f ≫ fb) (j ≫ (0 : _)) (f ≫ (0 : _)) (j ≫ jb)) ≫
              pairMap cm 0 0 cn := congrArg (fun x => x ≫ pairMap cm 0 0 cn) hfirst
          _ = (pairMap (f ≫ fb) 0 0 (j ≫ jb)) ≫ pairMap cm 0 0 cn := by
            simp only [comp_zero]
      _ = pairMap ((f ≫ fb) ≫ cm) 0 0 ((j ≫ jb) ≫ cn) := by
        rw [hsecond]
        simp only [comp_zero]
      _ = pairMap (RealShift.transition (d + d) (translate (-r.1) M)) 0 0
          (RealShift.transition (d + d) (translate (r.1 - (ε : ℝ)) N)) := by
        apply pairMap_ext
        · calc
            _ = translateToShiftStructure M (-r.1) (-r.1) (d + d) (by
                simp only [NNReal.coe_add]
                linarith [d.coe_nonneg]) :=
              translateToShiftStructure_comp_compIso M (-r.1) (-s.1) (-r.1) d
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by simp only [NNReal.coe_add]; linarith [d.coe_nonneg])
            _ = RealShift.transition (d + d) (translate (-r.1) M) :=
              translateToShiftStructure_self_transition M (-r.1) _ (by
                simp only [NNReal.coe_add]
                linarith [d.coe_nonneg])
        · simp
        · simp
        · calc
            _ = translateToShiftStructure N (r.1 - (ε : ℝ)) (r.1 - (ε : ℝ))
                (d + d) (by
                  simp only [NNReal.coe_add]
                  linarith [d.coe_nonneg]) :=
              translateToShiftStructure_comp_compIso N (r.1 - (ε : ℝ))
                (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ)) d
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by rw [show (d : ℝ) = r.1 - s.1 by rfl]; linarith)
                (by simp only [NNReal.coe_add]; linarith [d.coe_nonneg])
            _ = RealShift.transition (d + d) (translate (r.1 - (ε : ℝ)) N) :=
              translateToShiftStructure_self_transition N (r.1 - (ε : ℝ)) _ (by
                simp only [NNReal.coe_add]
                linarith [d.coe_nonneg])
  have hdiag := pairMap_diag_transition (translate (-r.1) M)
    (translate (r.1 - (ε : ℝ)) N) (d + d)
  exact hmatrix.trans hdiag

private def interpolationRelation (i : RealInterleaving ε M N)
    (s : InterpolationTime ε) : interpolationSource (k := k) (M := M) (N := N) s ⟶
      interpolationTarget (k := k) (M := M) (N := N) s := by
  let ms := s.1 - 2 * (ε : ℝ)
  let mt := -s.1
  let ns := -(ε : ℝ) - s.1
  let nt := s.1 - (ε : ℝ)
  have hm : ms ≤ mt := by dsimp [ms, mt]; linarith [s.2.2]
  have hn : ns ≤ nt := by dsimp [ns, nt]; linarith [s.2.1]
  have hφ : ms + (ε : ℝ) = nt := by dsimp [ms, nt]; ring
  have hψ : ns + (ε : ℝ) = mt := by dsimp [ns, mt]; ring
  exact pairMap
    (translateStructure M ms mt hm)
    (-translateInterleavingMap i.ψ ns mt hψ)
    (-translateInterleavingMap i.φ ms nt hφ)
    (translateStructure N ns nt hn)

private theorem interpolationRelation_naturality
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolationSourceForward (k := k) (M := M) (N := N) s r hsr ≫
        (shift (interpolationDelta s r hsr)).map (interpolationRelation i r) =
      interpolationRelation i s ≫ interpolationTargetForward
        (k := k) (M := M) (N := N) s r hsr := by
  unfold interpolationSourceForward interpolationTargetForward interpolationRelation
  dsimp only [interpolationSource, interpolationTarget]
  erw [shift_pairMap]
  erw [pairMap_diag_comp]
  erw [pairMap_comp_diag]
  apply pairMap_ext
  · exact translateStructure_shift_naturality M
      (s.1 - 2 * (ε : ℝ)) (r.1 - 2 * (ε : ℝ)) (-s.1) (-r.1)
      (interpolationDelta s r hsr)
      (by linarith [s.2.2])
      (by linarith [r.2.2])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)

  · have hψ := translateInterleavingMap_shift_naturality i.ψ
      (-(ε : ℝ) - s.1) (-(ε : ℝ) - r.1) (-s.1) (-r.1)
      (interpolationDelta s r hsr) (by ring) (by ring)
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)
    calc
      translateToShiftStructure N (-ε - s.1) (-ε - r.1)
          (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (-translateInterleavingMap i.ψ (-ε - r.1) (-r.1) _) =
        translateToShiftStructure N (-ε - s.1) (-ε - r.1)
          (interpolationDelta s r hsr) _ ≫
          (-((shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.ψ (-ε - r.1) (-r.1) _))) := by
              rw [shift_map_neg]
      _ = -(translateToShiftStructure N (-ε - s.1) (-ε - r.1)
          (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.ψ (-ε - r.1) (-r.1) _)) := by
              rw [Preadditive.comp_neg]
      _ = -((translateInterleavingMap i.ψ (-ε - s.1) (-s.1) _ ≫
          translateToShiftStructure M (-s.1) (-r.1)
            (interpolationDelta s r hsr) _)) := by rw [hψ.symm]
      _ = (-translateInterleavingMap i.ψ (-ε - s.1) (-s.1) _) ≫
          translateToShiftStructure M (-s.1) (-r.1)
            (interpolationDelta s r hsr) _ := by rw [Preadditive.neg_comp]
  · have hφ := translateInterleavingMap_shift_naturality i.φ
      (s.1 - 2 * (ε : ℝ)) (r.1 - 2 * (ε : ℝ))
      (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ)) (interpolationDelta s r hsr)
      (by ring) (by ring)
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
    calc
      translateToShiftStructure M (s.1 - 2 * (ε : ℝ)) (r.1 - 2 * (ε : ℝ))
          (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (-translateInterleavingMap i.φ (r.1 - 2 * (ε : ℝ))
              (r.1 - (ε : ℝ)) _) =
        translateToShiftStructure M (s.1 - 2 * (ε : ℝ))
          (r.1 - 2 * (ε : ℝ)) (interpolationDelta s r hsr) _ ≫
          (-((shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.φ (r.1 - 2 * (ε : ℝ))
              (r.1 - (ε : ℝ)) _))) := by rw [shift_map_neg]
      _ = -(translateToShiftStructure M (s.1 - 2 * (ε : ℝ))
          (r.1 - 2 * (ε : ℝ)) (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.φ (r.1 - 2 * (ε : ℝ))
              (r.1 - (ε : ℝ)) _)) := by rw [Preadditive.comp_neg]
      _ = -((translateInterleavingMap i.φ (s.1 - 2 * (ε : ℝ))
          (s.1 - (ε : ℝ)) _ ≫
          translateToShiftStructure N (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ))
            (interpolationDelta s r hsr) _)) := by rw [hφ.symm]
      _ = (-translateInterleavingMap i.φ (s.1 - 2 * (ε : ℝ))
          (s.1 - (ε : ℝ)) _) ≫
          translateToShiftStructure N (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ))
            (interpolationDelta s r hsr) _ := by rw [Preadditive.neg_comp]
  · exact translateStructure_shift_naturality N
      (-(ε : ℝ) - s.1) (-(ε : ℝ) - r.1)
      (s.1 - (ε : ℝ)) (r.1 - (ε : ℝ)) (interpolationDelta s r hsr)
      (by linarith [s.2.1])
      (by linarith [r.2.1])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)
private theorem interpolationRelation_reverse_naturality
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolationSourceBackward (k := k) (M := M) (N := N) s r hsr ≫
        (shift (interpolationDelta s r hsr)).map (interpolationRelation i s) =
      interpolationRelation i r ≫ interpolationTargetBackward
        (k := k) (M := M) (N := N) s r hsr := by
  unfold interpolationSourceBackward interpolationTargetBackward interpolationRelation
  dsimp only [interpolationSource, interpolationTarget]
  erw [shift_pairMap]
  erw [pairMap_diag_comp]
  erw [pairMap_comp_diag]
  apply pairMap_ext
  · exact translateStructure_shift_naturality M
      (r.1 - 2 * (ε : ℝ)) (s.1 - 2 * (ε : ℝ)) (-r.1) (-s.1)
      (interpolationDelta s r hsr)
      (by linarith [r.2.2])
      (by linarith [s.2.2])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
  · have hψ := translateInterleavingMap_shift_naturality i.ψ
      (-(ε : ℝ) - r.1) (-(ε : ℝ) - s.1) (-r.1) (-s.1)
      (interpolationDelta s r hsr) (by ring) (by ring)
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
    calc
      translateToShiftStructure N (-ε - r.1) (-ε - s.1)
          (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (-translateInterleavingMap i.ψ (-ε - s.1) (-s.1) _) =
        translateToShiftStructure N (-ε - r.1) (-ε - s.1)
          (interpolationDelta s r hsr) _ ≫
          (-((shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.ψ (-ε - s.1) (-s.1) _))) := by
              rw [shift_map_neg]
      _ = -(translateToShiftStructure N (-ε - r.1) (-ε - s.1)
          (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.ψ (-ε - s.1) (-s.1) _)) := by
              rw [Preadditive.comp_neg]
      _ = -((translateInterleavingMap i.ψ (-ε - r.1) (-r.1) _ ≫
          translateToShiftStructure M (-r.1) (-s.1)
            (interpolationDelta s r hsr) _)) := by rw [hψ.symm]
      _ = (-translateInterleavingMap i.ψ (-ε - r.1) (-r.1) _) ≫
          translateToShiftStructure M (-r.1) (-s.1)
            (interpolationDelta s r hsr) _ := by rw [Preadditive.neg_comp]
  · have hφ := translateInterleavingMap_shift_naturality i.φ
      (r.1 - 2 * (ε : ℝ)) (s.1 - 2 * (ε : ℝ))
      (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ)) (interpolationDelta s r hsr)
      (by ring) (by ring)
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)
    calc
      translateToShiftStructure M (r.1 - 2 * (ε : ℝ)) (s.1 - 2 * (ε : ℝ))
          (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (-translateInterleavingMap i.φ (s.1 - 2 * (ε : ℝ))
              (s.1 - (ε : ℝ)) _) =
        translateToShiftStructure M (r.1 - 2 * (ε : ℝ))
          (s.1 - 2 * (ε : ℝ)) (interpolationDelta s r hsr) _ ≫
          (-((shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.φ (s.1 - 2 * (ε : ℝ))
              (s.1 - (ε : ℝ)) _))) := by rw [shift_map_neg]
      _ = -(translateToShiftStructure M (r.1 - 2 * (ε : ℝ))
          (s.1 - 2 * (ε : ℝ)) (interpolationDelta s r hsr) _ ≫
          (shift (interpolationDelta s r hsr)).map
            (translateInterleavingMap i.φ (s.1 - 2 * (ε : ℝ))
              (s.1 - (ε : ℝ)) _)) := by rw [Preadditive.comp_neg]
      _ = -((translateInterleavingMap i.φ (r.1 - 2 * (ε : ℝ))
          (r.1 - (ε : ℝ)) _ ≫
          translateToShiftStructure N (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ))
            (interpolationDelta s r hsr) _)) := by rw [hφ.symm]
      _ = (-translateInterleavingMap i.φ (r.1 - 2 * (ε : ℝ))
          (r.1 - (ε : ℝ)) _) ≫
          translateToShiftStructure N (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ))
            (interpolationDelta s r hsr) _ := by rw [Preadditive.neg_comp]
  · exact translateStructure_shift_naturality N
      (-(ε : ℝ) - r.1) (-(ε : ℝ) - s.1)
      (r.1 - (ε : ℝ)) (s.1 - (ε : ℝ)) (interpolationDelta s r hsr)
      (by linarith [r.2.1])
      (by linarith [s.2.1])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith [hsr])
      (by rw [show (interpolationDelta s r hsr : ℝ) = r.1 - s.1 by rfl];
          linarith)


private abbrev startTime (ε : ℝ≥0) : InterpolationTime ε :=
  ⟨0, le_rfl, ε.coe_nonneg⟩

private abbrev endTime (ε : ℝ≥0) : InterpolationTime ε :=
  ⟨ε, ε.coe_nonneg, le_rfl⟩

private def translateZeroIso (P : PModule.{u,0,w} k ℝ) (a : ℝ) (ha : a = 0) :
    translate a P ≅ P :=
  reindexEqIso (a := translateOrder a) (b := OrderHom.id)
    (fun t => by change t + a = t; rw [ha, add_zero]) P

private def translateZeroMap (P : PModule.{u,0,w} k ℝ) (a : ℝ) (ha : a = 0) :
    translate a P ⟶ P :=
  (translateZeroIso P a ha).hom

private def endNZero : translate ((ε : ℝ) - (ε : ℝ)) N ⟶ N :=
  translateZeroMap N _ (sub_self _)

private def endPhi (i : RealInterleaving ε M N) :
    translate (-(ε : ℝ)) M ⟶ translate ((ε : ℝ) - (ε : ℝ)) N :=
  translateInterleavingMap i.φ (-(ε : ℝ)) ((ε : ℝ) - (ε : ℝ)) (by ring)

private def startCompare (i : RealInterleaving ε M N) :
    interpolationTarget (k := k) (M := M) (N := N) (startTime ε) ⟶ M :=
  pairDescMap (𝟙 (translate (-(startTime ε).1) M))
    (translateInterleavingMap i.ψ ((startTime ε).1 - (ε : ℝ)) (-(startTime ε).1)
      (by change (0 - (ε : ℝ)) + (ε : ℝ) = -0; ring)) ≫
    translateZeroMap M (-(startTime ε).1) (by exact neg_zero)

private theorem startN_offsets :
    (-(ε : ℝ) - (startTime ε).1) = (startTime ε).1 - (ε : ℝ) := by
  dsimp [startTime]
  ring

private noncomputable def startNTransport :
    translate ((startTime ε).1 - (ε : ℝ)) N ⟶
      translate (-(ε : ℝ) - (startTime ε).1) N :=
  (translateEqIso (startN_offsets (ε := ε)) N).inv

private theorem startNTransport_comp_psi (i : RealInterleaving ε M N) :
    startNTransport (ε := ε) (N := N) ≫
      translateInterleavingMap i.ψ (-(ε : ℝ) - (startTime ε).1)
        (-(startTime ε).1) (by dsimp [startTime]; ring) =
    translateInterleavingMap i.ψ ((startTime ε).1 - (ε : ℝ))
      (-(startTime ε).1) (by dsimp [startTime]; ring) := by
  exact translateEqIso_inv_comp_interleavingMap i.ψ _ _ _
    (by dsimp [startTime]; ring) (by dsimp [startTime]; ring) (startN_offsets (ε := ε))

private theorem startNTransport_comp_structure :
    startNTransport (ε := ε) (N := N) ≫
      translateStructure N (-(ε : ℝ) - (startTime ε).1)
        ((startTime ε).1 - (ε : ℝ)) (by rw [startN_offsets (ε := ε)]) =
    𝟙 (translate ((startTime ε).1 - (ε : ℝ)) N) := by
  exact translateEqIso_inv_comp_translateStructure N _ _
    (startN_offsets (ε := ε)) (by rw [startN_offsets (ε := ε)])

private theorem interpolationRelation_inr (i : RealInterleaving ε M N)
    (s : InterpolationTime ε) (hs : s.1 = 0) :
    (translateEqIso (show -(ε : ℝ) - s.1 = s.1 - (ε : ℝ) by rw [hs]; ring) N).inv ≫
      pairInr ≫ interpolationRelation i s =
    -(translateInterleavingMap i.ψ (s.1 - (ε : ℝ)) (-s.1)
        (by rw [hs]; ring) ≫ pairInl) + pairInr := by
  let ns := -(ε : ℝ) - s.1
  let nt := s.1 - (ε : ℝ)
  let mt := -s.1
  have hnsnt : ns = nt := by dsimp [ns, nt]; rw [hs]; ring
  have hψ := translateEqIso_inv_comp_interleavingMap i.ψ ns nt mt
    (by dsimp [ns, mt]; ring) (by dsimp [nt, mt]; rw [hs]; ring) hnsnt
  have hN := translateEqIso_inv_comp_translateStructure N ns nt hnsnt
    (le_of_eq hnsnt)
  have hψ' : (translateEqIso hnsnt N).inv ≫
      translateInterleavingMap i.ψ ns mt (by dsimp [ns, mt]; ring) =
      translateInterleavingMap i.ψ nt mt (by dsimp [nt, mt]; rw [hs]; ring) := by
    simpa [ns, nt, mt] using hψ
  have hN' : (translateEqIso hnsnt N).inv ≫
      translateStructure N ns nt (le_of_eq hnsnt) = 𝟙 (translate nt N) := by
    simpa [ns, nt] using hN
  dsimp only [interpolationRelation]
  rw [pairInr_comp_pairMap]
  dsimp [ns, nt, mt] at hψ hN ⊢
  rw [Preadditive.comp_add]
  rw [← Category.assoc (translateEqIso hnsnt N).inv
    (-translateInterleavingMap i.ψ ns mt (by dsimp [ns, mt]; ring)) pairInl]
  rw [← Category.assoc (translateEqIso hnsnt N).inv
    (translateStructure N ns nt (le_of_eq hnsnt)) pairInr]
  rw [Preadditive.comp_neg, hψ', hN']
  simp [nt, mt, Preadditive.comp_neg, Category.id_comp, Preadditive.neg_comp]

private theorem endRelation_inl (i : RealInterleaving ε M N) :
    (translateEqIso (show (ε : ℝ) - 2 * (ε : ℝ) = -(ε : ℝ) by ring) M).inv ≫
      pairInl ≫ interpolationRelation i (endTime ε) =
    pairInl + -(endPhi i ≫ pairInr) := by
  let ms := (ε : ℝ) - 2 * (ε : ℝ)
  let mt := -(ε : ℝ)
  let nt := (ε : ℝ) - (ε : ℝ)
  have hms : ms = mt := by dsimp [ms, mt]; ring
  have hφ := translateEqIso_inv_comp_interleavingMap i.φ ms mt nt
    (by dsimp [ms, nt]; ring) (by dsimp [mt, nt]; ring) hms
  have hM := translateEqIso_inv_comp_translateStructure M ms mt hms
    (le_of_eq hms)
  have hφ' : (translateEqIso hms M).inv ≫
      translateInterleavingMap i.φ ms nt (by dsimp [ms, nt]; ring) =
        translateInterleavingMap i.φ mt nt (by dsimp [mt, nt]; ring) := by
    simpa [ms, mt, nt] using hφ
  have hM' : (translateEqIso hms M).inv ≫
      translateStructure M ms mt (le_of_eq hms) = 𝟙 (translate mt M) := by
    simpa [ms, mt] using hM
  dsimp only [interpolationRelation]
  rw [pairInl_comp_pairMap]
  dsimp [ms, mt, nt] at hφ hM ⊢
  rw [Preadditive.comp_add]
  rw [← Category.assoc (translateEqIso hms M).inv
    (translateStructure M ms mt (le_of_eq hms)) pairInl]
  rw [← Category.assoc (translateEqIso hms M).inv
    (-translateInterleavingMap i.φ ms nt (by dsimp [ms, nt]; ring)) pairInr]
  rw [Preadditive.comp_neg, hM', hφ']
  simp [endPhi, mt, nt, Preadditive.comp_neg, Category.id_comp, Preadditive.neg_comp]

private theorem startCompare_kills (i : RealInterleaving ε M N) :
    interpolationRelation i (startTime ε) ≫ startCompare i = 0 := by
  unfold startCompare
  erw [← Category.assoc]
  suffices interpolationRelation i (startTime ε) ≫
      pairDescMap (𝟙 (translate (-(startTime ε).1) M))
        (translateInterleavingMap i.ψ ((startTime ε).1 - (ε : ℝ)) (-(startTime ε).1)
          (by change (0 - (ε : ℝ)) + (ε : ℝ) = -0; ring)) = 0 by
    rw [this, zero_comp]
  unfold interpolationRelation
  dsimp only [startTime]
  apply pairMap_comp_pairDescMap_zero
  · rw [Preadditive.neg_comp, translateInterleavingMap_comp]
  · rw [neg_neg]
    exact translateStructure_comp_interleavingMap i.ψ _ _ _ _ _ _

/-- The quotient interpolation module `F_s`.  Its fiber at `t` is the quotient
of `M(t-s) × N(t-ε+s)` by the image of the signed interleaving relation from
`M(t-2ε+s) × N(t-ε-s)`. -/
noncomputable def interpolatingModule (i : RealInterleaving ε M N)
    (s : InterpolationTime ε) : PModule.{u,0,w} k ℝ :=
  cokernel (interpolationRelation i s)

private noncomputable def startProjection (i : RealInterleaving ε M N) :
    pairModule (translate (-(startTime ε).1) M)
      (translate ((startTime ε).1 - (ε : ℝ)) N) ⟶
    interpolatingModule i (startTime ε) :=
  cokernel.π (interpolationRelation i (startTime ε))

private noncomputable def startInclude (i : RealInterleaving ε M N) :
    M ⟶ interpolatingModule i (startTime ε) :=
  (translateZeroIso M (-(startTime ε).1) (by exact neg_zero)).inv ≫
    pairInl (P := translate (-(startTime ε).1) M)
      (Q := translate ((startTime ε).1 - (ε : ℝ)) N) ≫
    startProjection i

private noncomputable def startDesc (i : RealInterleaving ε M N) :
    interpolatingModule i (startTime ε) ⟶ M :=
  cokernel.desc (interpolationRelation i (startTime ε)) (startCompare i)
    (startCompare_kills i)

private theorem startInclude_comp_startDesc (i : RealInterleaving ε M N) :
    startInclude i ≫ startDesc i = 𝟙 M := by
  unfold startInclude startDesc interpolatingModule
  dsimp only [startTime, interpolationTarget]
  simp only [Category.assoc, startProjection, cokernel.π_desc, startCompare]
  rw [← Category.assoc pairInl]
  rw [pairInl_pairDescMap]
  simp [translateZeroMap, Category.assoc]

private theorem startCompare_comp_startInclude (i : RealInterleaving ε M N) :
    startCompare i ≫ startInclude i = startProjection i := by
  apply pairModule_hom_ext
  · unfold startCompare startInclude
    rw [pairInl_pairDescMap_comp_comp]
    simp [translateZeroMap, Iso.hom_inv_id_assoc, Category.assoc]
  · let ψ₀ := translateInterleavingMap i.ψ ((startTime ε).1 - (ε : ℝ))
      (-(startTime ε).1) (by dsimp [startTime]; ring)
    have hrel := interpolationRelation_inr i (startTime ε)
      (by dsimp [startTime])
    have hzero : (-(ψ₀ ≫ pairInl) + pairInr) ≫
        cokernel.π (interpolationRelation i (startTime ε)) = 0 := by
      calc
        _ = (startNTransport (ε := ε) (N := N) ≫ pairInr ≫
            interpolationRelation i (startTime ε)) ≫
              cokernel.π (interpolationRelation i (startTime ε)) := by
                exact congrArg (fun f => f ≫
                  cokernel.π (interpolationRelation i (startTime ε))) hrel.symm
        _ = startNTransport (ε := ε) (N := N) ≫ pairInr ≫
            (interpolationRelation i (startTime ε) ≫
              cokernel.π (interpolationRelation i (startTime ε))) := by
                simp [Category.assoc]
        _ = 0 := by simp [cokernel.condition]
    have hcol : (ψ₀ ≫ pairInl) ≫
        cokernel.π (interpolationRelation i (startTime ε)) =
      pairInr ≫ cokernel.π (interpolationRelation i (startTime ε)) := by
      have hz : -((ψ₀ ≫ pairInl) ≫
          cokernel.π (interpolationRelation i (startTime ε))) +
          (pairInr ≫ cokernel.π (interpolationRelation i (startTime ε))) = 0 := by
        simpa [Category.assoc] using hzero
      calc
        (ψ₀ ≫ pairInl) ≫ cokernel.π (interpolationRelation i (startTime ε)) =
            (ψ₀ ≫ pairInl) ≫ cokernel.π (interpolationRelation i (startTime ε)) + 0 := by simp
        _ = (ψ₀ ≫ pairInl) ≫ cokernel.π (interpolationRelation i (startTime ε)) +
            (-(ψ₀ ≫ pairInl) ≫ cokernel.π (interpolationRelation i (startTime ε)) +
              pairInr ≫ cokernel.π (interpolationRelation i (startTime ε))) := by rw [hz]
        _ = pairInr ≫ cokernel.π (interpolationRelation i (startTime ε)) := by abel
    have hcol' : (ψ₀ ≫ pairInl) ≫ startProjection i =
        pairInr ≫ startProjection i := by
      simpa [startProjection, interpolatingModule] using hcol
    calc
      pairInr ≫ startCompare i ≫ startInclude i =
          (ψ₀ ≫ pairInl) ≫ startProjection i := by
            unfold startCompare startInclude
            rw [pairInr_pairDescMap_comp_comp]
            dsimp only [startTime]
            simp [startProjection, startTime, ψ₀, translateZeroMap,
              Iso.hom_inv_id_assoc, Category.assoc]
            exact Category.assoc _ _ _
      _ = pairInr ≫ startProjection i := hcol'

private theorem startDesc_comp_startInclude (i : RealInterleaving ε M N) :
    startDesc i ≫ startInclude i = 𝟙 (interpolatingModule i (startTime ε)) := by
  have h_epi : Epi (startProjection i) := by
    change Epi (cokernel.π (interpolationRelation i (startTime ε)))
    infer_instance
  letI := h_epi
  apply (cancel_epi (startProjection i)).1
  rw [← Category.assoc]
  rw [show startProjection i ≫ startDesc i = startCompare i by
    simp [startProjection, startDesc, interpolatingModule]]
  rw [startCompare_comp_startInclude]
  simp

private def endCompare (i : RealInterleaving ε M N) :
    interpolationTarget (k := k) (M := M) (N := N) (endTime ε) ⟶ N :=
  pairDescMap (endPhi i ≫ endNZero (N := N)) (endNZero (N := N))

private theorem endCompare_kills (i : RealInterleaving ε M N) :
    interpolationRelation i (endTime ε) ≫ endCompare i = 0 := by
  let ms := (ε : ℝ) - 2 * (ε : ℝ)
  let mt := -(ε : ℝ)
  let n := -(ε : ℝ) - (ε : ℝ)
  let c := (ε : ℝ) - (ε : ℝ)
  let ψ₀ := translateInterleavingMap i.ψ n mt (by dsimp [n, mt]; ring)
  let φ₀ := translateInterleavingMap i.φ ms c (by dsimp [ms, c]; ring)
  have hMcomp : translateStructure M ms mt (by dsimp [ms, mt]; linarith [ε.coe_nonneg])
      ≫ endPhi i = φ₀ := by
    exact translateStructure_comp_interleavingMap i.φ ms mt c
      (by dsimp [ms, mt]; linarith [ε.coe_nonneg]) (by dsimp [mt, c]; ring)
      (by dsimp [ms, c]; linarith [ε.coe_nonneg])
  have hNcomp : ψ₀ ≫ endPhi i =
      translateStructure N n c (by dsimp [n, c]; linarith [ε.coe_nonneg]) := by
    exact translateInterleavingMap_ψφ_comp i n mt c
      (by dsimp [n, mt]; ring) (by dsimp [mt, c]; ring)
      (by dsimp [n, c]; linarith [ε.coe_nonneg])
  have hfirst : translateStructure M ms mt (by dsimp [ms, mt]; linarith [ε.coe_nonneg]) ≫
      (endPhi i ≫ endNZero (N := N)) =
      -((-φ₀) ≫ endNZero (N := N)) := by
    rw [← Category.assoc, hMcomp]
    simp [Preadditive.neg_comp]
  have hsecond : -ψ₀ ≫ (endPhi i ≫ endNZero (N := N)) =
      -(translateStructure N n c (by dsimp [n, c]; linarith [ε.coe_nonneg]) ≫
        endNZero (N := N)) := by
    apply neg_injective
    rw [← Category.assoc, hNcomp]
  unfold endCompare interpolationRelation
  dsimp only [endTime]
  apply pairMap_comp_pairDescMap_zero_general
  · simpa [ms, mt, c, φ₀, Preadditive.neg_comp, Category.assoc] using hfirst
  · simpa [n, c, ψ₀, φ₀, Preadditive.neg_comp, Category.assoc] using hsecond

private noncomputable def endProjection (i : RealInterleaving ε M N) :
    pairModule (translate (-(ε : ℝ)) M) (translate ((ε : ℝ) - (ε : ℝ)) N) ⟶
      interpolatingModule i (endTime ε) :=
  cokernel.π (interpolationRelation i (endTime ε))

private noncomputable def endInclude (i : RealInterleaving ε M N) :
    N ⟶ interpolatingModule i (endTime ε) :=
  (translateZeroIso N ((ε : ℝ) - (ε : ℝ)) (sub_self _)).inv ≫
    pairInr (P := translate (-(ε : ℝ)) M)
      (Q := translate ((ε : ℝ) - (ε : ℝ)) N) ≫ endProjection i

private noncomputable def endDesc (i : RealInterleaving ε M N) :
    interpolatingModule i (endTime ε) ⟶ N :=
  cokernel.desc (interpolationRelation i (endTime ε)) (endCompare i)
    (endCompare_kills i)

private theorem endInclude_comp_endDesc (i : RealInterleaving ε M N) :
    endInclude i ≫ endDesc i = 𝟙 N := by
  unfold endInclude endDesc interpolatingModule
  dsimp only [endTime, interpolationTarget]
  simp only [Category.assoc, endProjection, cokernel.π_desc, endCompare]
  rw [pairInr_pairDescMap]
  simp [endNZero, translateZeroMap, Category.assoc]

private theorem endCompare_comp_endInclude (i : RealInterleaving ε M N) :
    endCompare i ≫ endInclude i = endProjection i := by
  apply pairModule_hom_ext
  · let τ := (translateEqIso
      (show (ε : ℝ) - 2 * (ε : ℝ) = -(ε : ℝ) by ring) M).inv
    have hrel := endRelation_inl i
    have hzero : (pairInl + -(endPhi i ≫ pairInr)) ≫
        cokernel.π (interpolationRelation i (endTime ε)) = 0 := by
      calc
        _ = (τ ≫ pairInl ≫ interpolationRelation i (endTime ε)) ≫
            cokernel.π (interpolationRelation i (endTime ε)) := by
              exact congrArg (fun f => f ≫
                cokernel.π (interpolationRelation i (endTime ε))) hrel.symm
        _ = τ ≫ pairInl ≫
            (interpolationRelation i (endTime ε) ≫
              cokernel.π (interpolationRelation i (endTime ε))) := by
                simp [Category.assoc]
        _ = 0 := by simp [cokernel.condition]
    have hcol : pairInl ≫ cokernel.π (interpolationRelation i (endTime ε)) =
        (endPhi i ≫ pairInr) ≫ cokernel.π (interpolationRelation i (endTime ε)) := by
      have hz : (pairInl ≫ cokernel.π (interpolationRelation i (endTime ε))) +
          -((endPhi i ≫ pairInr) ≫
            cokernel.π (interpolationRelation i (endTime ε))) = 0 := by
        simpa [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc] using hzero
      calc
        pairInl ≫ cokernel.π (interpolationRelation i (endTime ε)) =
            (pairInl ≫ cokernel.π (interpolationRelation i (endTime ε)) +
              -(endPhi i ≫ pairInr) ≫
                cokernel.π (interpolationRelation i (endTime ε))) +
              (endPhi i ≫ pairInr) ≫
                cokernel.π (interpolationRelation i (endTime ε)) := by
                  simp [Category.assoc, Preadditive.comp_neg]
        _ = (endPhi i ≫ pairInr) ≫
            cokernel.π (interpolationRelation i (endTime ε)) := by
              rw [hz]
              simp
    calc
      pairInl ≫ endCompare i ≫ endInclude i =
          (endPhi i ≫ pairInr) ≫ endProjection i := by
            unfold endCompare endInclude
            rw [← Category.assoc pairInl]
            rw [pairInl_pairDescMap]
            simp [endProjection, endNZero, translateZeroMap,
              Iso.hom_inv_id_assoc, Category.assoc]
            exact (Category.assoc _ _ _).symm
      _ = pairInl ≫ endProjection i := by
        simpa [endProjection, interpolatingModule, Category.assoc] using hcol.symm
  · unfold endCompare endInclude
    rw [← Category.assoc pairInr]
    rw [pairInr_pairDescMap]
    simp [endProjection, endNZero, translateZeroMap,
      Iso.hom_inv_id_assoc, Category.assoc]

private theorem endDesc_comp_endInclude (i : RealInterleaving ε M N) :
    endDesc i ≫ endInclude i = 𝟙 (interpolatingModule i (endTime ε)) := by
  have h_epi : Epi (endProjection i) := by
    change Epi (cokernel.π (interpolationRelation i (endTime ε)))
    infer_instance
  letI := h_epi
  apply (cancel_epi (endProjection i)).1
  rw [← Category.assoc]
  rw [show endProjection i ≫ endDesc i = endCompare i by
    simp [endProjection, endDesc, interpolatingModule]]
  rw [endCompare_comp_endInclude]
  simp

private noncomputable def startIso (i : RealInterleaving ε M N) :
    interpolatingModule i (startTime ε) ≅ M where
  hom := startDesc i
  inv := startInclude i
  hom_inv_id := startDesc_comp_startInclude i
  inv_hom_id := startInclude_comp_startDesc i

private noncomputable def endIso (i : RealInterleaving ε M N) :
    interpolatingModule i (endTime ε) ≅ N where
  hom := endDesc i
  inv := endInclude i
  hom_inv_id := endDesc_comp_endInclude i
  inv_hom_id := endInclude_comp_endDesc i

private theorem translate_qTame (P : PModule.{u,0,w} k ℝ) (hP : P.QTame) (c : ℝ) :
    (translate c P).QTame := by
  intro a b hab
  have hlt : a + c < b + c := by linarith
  have h := hP (a + c) (b + c) hlt
  change FiniteDimensional k (LinearMap.range
    (structureMapLinear (reindex (translateOrder c) P) hab.le))
  rw [structureMapLinear_reindex]
  exact h

private theorem pairModule_qTame {P Q : PModule.{u,0,w} k ℝ}
    (hP : P.QTame) (hQ : Q.QTame) : (pairModule P Q).QTame := by
  intro a b hab
  let f := structureMapLinear P hab.le
  let g := structureMapLinear Q hab.le
  have hf : FiniteDimensional k (LinearMap.range f) := hP a b hab
  have hg : FiniteDimensional k (LinearMap.range g) := hQ a b hab
  letI := hf
  letI := hg
  change FiniteDimensional k (LinearMap.range (f.prodMap g))
  rw [LinearMap.range_prodMap]
  have hp : FiniteDimensional k (↥(LinearMap.range f) × ↥(LinearMap.range g)) := by
    infer_instance
  letI := hp
  exact FiniteDimensional.of_injective
    (submoduleProdEquiv (LinearMap.range f) (LinearMap.range g)).toLinearMap
    (submoduleProdEquiv (LinearMap.range f) (LinearMap.range g)).injective

private theorem qTame_cokernel {A B : PModule.{u,0,w} k ℝ} (f : A ⟶ B)
    (hB : B.QTame) : (cokernel f).QTame := by
  intro a b hab
  let πa := (cokernel.π f).app a
  let πb := (cokernel.π f).app b
  let g := structureMapLinear B hab.le
  let L := structureMapLinear (cokernel f) hab.le
  have hπ : Function.Surjective πa.hom := by
    have h_epi : Epi (cokernel.π f) := by infer_instance
    exact (ModuleCat.epi_iff_surjective _).mp
      ((NatTrans.epi_iff_epi_app (cokernel.π f)).mp h_epi a)
  have hcomp : L.comp πa.hom = πb.hom.comp g := by
    have hn := (cokernel.π f).naturality (homOfLE hab.le)
    change B.map (homOfLE hab.le) ≫ (cokernel.π f).app b =
      (cokernel.π f).app a ≫ (cokernel f).map (homOfLE hab.le) at hn
    have hn' := congrArg ModuleCat.Hom.hom hn
    change πb.hom.comp g = L.comp πa.hom at hn'
    exact hn'.symm
  have hrange : LinearMap.range L = LinearMap.range (πb.hom.comp g) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨z, hz⟩ := hπ x
      refine ⟨z, ?_⟩
      change πb.hom (g z) = L x
      rw [← hz]
      exact (congrArg (fun q => q z) hcomp).symm
    · rintro ⟨x, rfl⟩
      refine ⟨πa.hom x, ?_⟩
      change L (πa.hom x) = πb.hom (g x)
      exact congrArg (fun q => q x) hcomp
  have hg : FiniteDimensional k (LinearMap.range g) := hB a b hab
  letI := hg
  let gr : B.obj a →ₗ[k] LinearMap.range g :=
    g.codRestrict (LinearMap.range g) (fun x => ⟨x, rfl⟩)
  have hfactor : πb.hom.comp g =
      (πb.hom.comp (LinearMap.range g).subtype).comp gr := by
    ext x
    rfl
  rw [hrange, hfactor]
  exact finiteDimensional_range_of_factorization _ _ _ rfl

/-- Every module in the quotient interpolation family is q-tame. -/
theorem interpolatingModule_qTame (i : RealInterleaving ε M N)
    (hM : M.QTame) (hN : N.QTame) (s : InterpolationTime ε) :
    (interpolatingModule i s).QTame := by
  apply qTame_cokernel (interpolationRelation i s)
  exact pairModule_qTame (translate_qTame M hM (-s.1))
    (translate_qTame N hN (s.1 - (ε : ℝ)))

private noncomputable def interpolatingProjection
    (i : RealInterleaving ε M N) (s : InterpolationTime ε) :
    interpolationTarget (k := k) (M := M) (N := N) s ⟶ interpolatingModule i s :=
  cokernel.π (interpolationRelation i s)

private noncomputable def interpolatingMapOfLe
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolatingModule i s ⟶
      (shift (interpolationDelta s r hsr)).obj (interpolatingModule i r) := by
  unfold interpolatingModule
  refine cokernel.desc (interpolationRelation i s)
    (interpolationTargetForward (k := k) (M := M) (N := N) s r hsr ≫
      (shift (interpolationDelta s r hsr)).map
        (cokernel.π (interpolationRelation i r))) ?_
  rw [← Category.assoc]
  rw [← interpolationRelation_naturality]
  rw [Category.assoc, ← Functor.map_comp]
  simp [cokernel.condition, shift_map_zero]

private noncomputable def interpolatingMapReverse
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolatingModule i r ⟶
      (shift (interpolationDelta s r hsr)).obj (interpolatingModule i s) := by
  unfold interpolatingModule
  refine cokernel.desc (interpolationRelation i r)
    (interpolationTargetBackward (k := k) (M := M) (N := N) s r hsr ≫
      (shift (interpolationDelta s r hsr)).map
        (cokernel.π (interpolationRelation i s))) ?_
  rw [← Category.assoc]
  rw [← interpolationRelation_reverse_naturality]
  rw [Category.assoc, ← Functor.map_comp]
  simp [cokernel.condition, shift_map_zero]

private theorem interpolatingMapOfLe_projection
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolatingProjection i s ≫ interpolatingMapOfLe i s r hsr =
      interpolationTargetForward (k := k) (M := M) (N := N) s r hsr ≫
        (shift (interpolationDelta s r hsr)).map
          (interpolatingProjection i r) := by
  simp [interpolatingMapOfLe, interpolatingProjection, interpolatingModule, Category.assoc]

private theorem interpolatingMapReverse_projection
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolatingProjection i r ≫ interpolatingMapReverse i s r hsr =
      interpolationTargetBackward (k := k) (M := M) (N := N) s r hsr ≫
        (shift (interpolationDelta s r hsr)).map
          (interpolatingProjection i s) := by
  simp [interpolatingMapReverse, interpolatingProjection, interpolatingModule, Category.assoc]

private theorem interpolatingMapOfLe_reverse_comp
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolatingMapOfLe i s r hsr ≫
        (shift (interpolationDelta s r hsr)).map
          (interpolatingMapReverse i s r hsr) ≫
        (RealShift.compIso (interpolationDelta s r hsr)
          (interpolationDelta s r hsr) (interpolatingModule i s)).hom =
      RealShift.transition (interpolationDelta s r hsr + interpolationDelta s r hsr)
        (interpolatingModule i s) := by
  let d := interpolationDelta s r hsr
  let ps := interpolatingProjection i s
  let pr := interpolatingProjection i r
  let tf := interpolationTargetForward (k := k) (M := M) (N := N) s r hsr
  let tb := interpolationTargetBackward (k := k) (M := M) (N := N) s r hsr
  let mf := interpolatingMapOfLe i s r hsr
  let mb := interpolatingMapReverse i s r hsr
  let sr := (shift d).map pr
  let sp := (shift d).map ps
  let sg := (shift d).map mb
  let tbf := (shift d).map tb
  let ssf := (shift d).map sp
  let cq := (RealShift.compIso d d (interpolatingModule i s)).hom
  let ct := (RealShift.compIso d d
    (interpolationTarget (k := k) (M := M) (N := N) s)).hom
  let p2 := (shift (d + d)).map ps
  have h_epi : Epi ps := by
    dsimp [ps, interpolatingProjection, interpolatingModule]
    infer_instance
  letI := h_epi
  have hprojf : ps ≫ mf = tf ≫ sr :=
    interpolatingMapOfLe_projection i s r hsr
  have hprojb : pr ≫ mb = tb ≫ sp :=
    interpolatingMapReverse_projection i s r hsr
  have hmap : sr ≫ sg = (shift d).map (pr ≫ mb) := by
    rw [← Functor.map_comp]
  have hexpand : (shift d).map (tb ≫ sp) = tbf ≫ ssf := by
    rw [Functor.map_comp]
  have hcompIso := RealShift.compIso_naturality d d ps
  have htarget := interpolationTarget_forward_backward_comp
    (k := k) (M := M) (N := N) s r hsr
  have htarget' : (tf ≫ tbf) ≫ ct =
      RealShift.transition (d + d) (interpolationTarget s) :=
    (Category.assoc tf tbf ct).trans htarget
  apply (cancel_epi ps).1
  change ps ≫ mf ≫ sg ≫ cq =
    ps ≫ RealShift.transition (d + d) (interpolatingModule i s)
  calc
    _ = ((ps ≫ mf) ≫ sg) ≫ cq := by
      exact (Category.assoc ps mf (sg ≫ cq)).symm.trans
        (Category.assoc (ps ≫ mf) sg cq).symm
    _ = ((tf ≫ sr) ≫ sg) ≫ cq :=
      congrArg (fun f => (f ≫ sg) ≫ cq) hprojf
    _ = (tf ≫ (sr ≫ sg)) ≫ cq :=
      congrArg (fun f => f ≫ cq) (Category.assoc tf sr sg)
    _ = (tf ≫ (shift d).map (pr ≫ mb)) ≫ cq :=
      congrArg (fun f => (tf ≫ f) ≫ cq) hmap
    _ = (tf ≫ (shift d).map (tb ≫ sp)) ≫ cq :=
      congrArg (fun f => (tf ≫ f) ≫ cq)
        (congrArg ((shift d).map) hprojb)
    _ = (tf ≫ (tbf ≫ ssf)) ≫ cq :=
      congrArg (fun f => (tf ≫ f) ≫ cq) hexpand
    _ = ((tf ≫ tbf) ≫ ssf) ≫ cq :=
      congrArg (fun f => f ≫ cq) (Category.assoc tf tbf ssf).symm
    _ = (tf ≫ tbf) ≫ (ssf ≫ cq) := Category.assoc (tf ≫ tbf) ssf cq
    _ = (tf ≫ tbf) ≫ (ct ≫ p2) :=
      congrArg (fun f => (tf ≫ tbf) ≫ f) hcompIso
    _ = ((tf ≫ tbf) ≫ ct) ≫ p2 :=
      (Category.assoc (tf ≫ tbf) ct p2).symm
    _ = RealShift.transition (d + d) (interpolationTarget s) ≫ p2 :=
      congrArg (fun f => f ≫ p2) htarget'
    _ = ps ≫ RealShift.transition (d + d) (interpolatingModule i s) :=
      (RealShift.transition_naturality (d + d) ps).symm

private theorem interpolatingMapReverse_forward_comp
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε)
    (hsr : s.1 ≤ r.1) :
    interpolatingMapReverse i s r hsr ≫
        (shift (interpolationDelta s r hsr)).map
          (interpolatingMapOfLe i s r hsr) ≫
        (RealShift.compIso (interpolationDelta s r hsr)
          (interpolationDelta s r hsr) (interpolatingModule i r)).hom =
      RealShift.transition (interpolationDelta s r hsr + interpolationDelta s r hsr)
        (interpolatingModule i r) := by
  let d := interpolationDelta s r hsr
  let ps := interpolatingProjection i s
  let pr := interpolatingProjection i r
  let tf := interpolationTargetForward (k := k) (M := M) (N := N) s r hsr
  let tb := interpolationTargetBackward (k := k) (M := M) (N := N) s r hsr
  let mf := interpolatingMapOfLe i s r hsr
  let mb := interpolatingMapReverse i s r hsr
  let sp := (shift d).map ps
  let sr := (shift d).map pr
  let sg := (shift d).map mf
  let tbf := (shift d).map tf
  let ssr := (shift d).map sr
  let cq := (RealShift.compIso d d (interpolatingModule i r)).hom
  let ct := (RealShift.compIso d d
    (interpolationTarget (k := k) (M := M) (N := N) r)).hom
  let p2 := (shift (d + d)).map pr
  have h_epi : Epi pr := by
    dsimp [pr, interpolatingProjection, interpolatingModule]
    infer_instance
  letI := h_epi
  have hprojf : ps ≫ mf = tf ≫ sr :=
    interpolatingMapOfLe_projection i s r hsr
  have hprojb : pr ≫ mb = tb ≫ sp :=
    interpolatingMapReverse_projection i s r hsr
  have hmap : sp ≫ sg = (shift d).map (ps ≫ mf) := by
    rw [← Functor.map_comp]
  have hexpand : (shift d).map (tf ≫ sr) = tbf ≫ ssr := by
    rw [Functor.map_comp]
  have hcompIso := RealShift.compIso_naturality d d pr
  have htarget := interpolationTarget_backward_forward_comp
    (k := k) (M := M) (N := N) s r hsr
  have htarget' : (tb ≫ tbf) ≫ ct =
      RealShift.transition (d + d) (interpolationTarget (k := k) (M := M) (N := N) r) :=
    (Category.assoc tb tbf ct).trans htarget
  apply (cancel_epi pr).1
  change pr ≫ mb ≫ sg ≫ cq =
    pr ≫ RealShift.transition (d + d) (interpolatingModule i r)
  calc
    _ = ((pr ≫ mb) ≫ sg) ≫ cq := by
      exact (Category.assoc pr mb (sg ≫ cq)).symm.trans
        (Category.assoc (pr ≫ mb) sg cq).symm
    _ = ((tb ≫ sp) ≫ sg) ≫ cq :=
      congrArg (fun f => (f ≫ sg) ≫ cq) hprojb
    _ = (tb ≫ (sp ≫ sg)) ≫ cq :=
      congrArg (fun f => f ≫ cq) (Category.assoc tb sp sg)
    _ = (tb ≫ (shift d).map (ps ≫ mf)) ≫ cq :=
      congrArg (fun f => (tb ≫ f) ≫ cq) hmap
    _ = (tb ≫ (shift d).map (tf ≫ sr)) ≫ cq :=
      congrArg (fun f => (tb ≫ f) ≫ cq)
        (congrArg ((shift d).map) hprojf)
    _ = (tb ≫ (tbf ≫ ssr)) ≫ cq :=
      congrArg (fun f => (tb ≫ f) ≫ cq) hexpand
    _ = ((tb ≫ tbf) ≫ ssr) ≫ cq :=
      congrArg (fun f => f ≫ cq) (Category.assoc tb tbf ssr).symm
    _ = (tb ≫ tbf) ≫ (ssr ≫ cq) := Category.assoc (tb ≫ tbf) ssr cq
    _ = (tb ≫ tbf) ≫ (ct ≫ p2) :=
      congrArg (fun f => (tb ≫ tbf) ≫ f) hcompIso
    _ = ((tb ≫ tbf) ≫ ct) ≫ p2 :=
      (Category.assoc (tb ≫ tbf) ct p2).symm
    _ = RealShift.transition (d + d)
          (interpolationTarget (k := k) (M := M) (N := N) r) ≫ p2 :=
      congrArg (fun f => f ≫ p2) htarget'
    _ = pr ≫ RealShift.transition (d + d) (interpolatingModule i r) :=
      (RealShift.transition_naturality (d + d) pr).symm

private def reparamInterleaving {d e : ℝ≥0}
    {P Q : PModule.{u,0,w} k ℝ} (h : d = e) :
    RealInterleaving d P Q → RealInterleaving e P Q := by
  intro j
  cases h
  exact j

private noncomputable def interpolatingModules_interleaved
    (i : RealInterleaving ε M N) (s r : InterpolationTime ε) :
    RealInterleaving (nndist s.1 r.1) (interpolatingModule i s)
      (interpolatingModule i r) := by
  by_cases hsr : s.1 ≤ r.1
  · let d := interpolationDelta s r hsr
    let j : RealInterleaving d (interpolatingModule i s) (interpolatingModule i r) :=
      ⟨interpolatingMapOfLe i s r hsr, interpolatingMapReverse i s r hsr,
        interpolatingMapOfLe_reverse_comp i s r hsr,
        interpolatingMapReverse_forward_comp i s r hsr⟩
    exact reparamInterleaving (interpolationDelta_eq_nndist s r hsr) j
  · have hrs : r.1 ≤ s.1 := le_of_not_ge hsr
    let d := interpolationDelta r s hrs
    let j : RealInterleaving d (interpolatingModule i r) (interpolatingModule i s) :=
      ⟨interpolatingMapOfLe i r s hrs, interpolatingMapReverse i r s hrs,
        interpolatingMapOfLe_reverse_comp i r s hrs,
        interpolatingMapReverse_forward_comp i r s hrs⟩
    have hd : d = nndist s.1 r.1 := by
      change interpolationDelta r s hrs = nndist s.1 r.1
      rw [interpolationDelta_eq_nndist r s hrs, nndist_comm]
    exact reparamInterleaving hd j.symm

/-- An actual ε-interleaving of q-tame real modules produces an algebraic
q-tame interpolation on the closed parameter interval.  The endpoint modules
are naturally isomorphic to the inputs, and every pair of family members is
actually interleaved by their nonnegative real parameter distance. -/
theorem exists_qTame_interpolating_family
    (i : RealInterleaving ε M N) (hM : M.QTame) (hN : N.QTame) :
    ∃ F : InterpolationTime ε → PModule.{u,0,w} k ℝ,
      Nonempty (F (startTime ε) ≅ M) ∧ Nonempty (F (endTime ε) ≅ N) ∧
      (∀ s, (F s).QTame) ∧
      (∀ s r, Nonempty (RealInterleaving (nndist s.1 r.1) (F s) (F r))) := by
  refine ⟨interpolatingModule i, ⟨startIso i⟩, ⟨endIso i⟩, ?_, ?_⟩
  · intro s
    exact interpolatingModule_qTame i hM hN s
  · intro s r
    exact ⟨interpolatingModules_interleaved i s r⟩

end TDA.Persistence.RealInterleaving
