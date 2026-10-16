import TDA.Persistence.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Real shifts and interleaving witnesses

Shifts are actual reindexings by `t ↦ t + ε`. The canonical index identifications
and the original structure maps supply the coherence and transition maps. Parameters
are finite nonnegative reals. No interleaving distance is defined here.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject NNReal

namespace RealShift

variable {R : Type u} [Ring R]

/-- Translation by a finite nonnegative real, in the positive evaluation direction. -/
def translation (ε : ℝ≥0) : ℝ →o ℝ :=
  ⟨fun t => t + (ε : ℝ), fun _ _ h => add_le_add h le_rfl⟩

/-- Translation has the declared positive evaluation direction. -/
@[simp] theorem translation_apply (ε : ℝ≥0) (t : ℝ) : translation ε t = t + (ε : ℝ) := rfl

/-- The real shift endofunctor, including its action on natural transformations. -/
def shift (ε : ℝ≥0) : PModule.{u,0,w} R ℝ ⥤ PModule.{u,0,w} R ℝ where
  obj M := reindex (translation ε) M
  map f := reindexNatTrans (translation ε) f

/-- A shift evaluates the original module at the translated real parameter. -/
@[simp] theorem shift_obj (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    ((shift ε).obj M).obj t = M.obj (t + (ε : ℝ)) := rfl

/-- Shifted transformations use the actual translated components. -/
@[simp] theorem shift_map_app (ε : ℝ≥0) {M N : PModule.{u,0,w} R ℝ}
    (f : M ⟶ N) (t : ℝ) : ((shift ε).map f).app t = f.app (t + (ε : ℝ)) := rfl

/-- Shifted structure maps are the original maps between translated parameters. -/
theorem shift_structureMap (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) {s t : ℝ} (h : s ≤ t) :
    structureMap ((shift ε).obj M) h = structureMap M (add_le_add h le_rfl) := rfl

private def reindexIso {a b : ℝ →o ℝ} (h : ∀ t, a t = b t)
    (M : PModule.{u,0,w} R ℝ) : reindex a M ≅ reindex b M :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun t => eqToIso (h t)) (by intros; apply Subsingleton.elim)) M

/-- The canonical zero-shift identification is induced by `t + 0 = t`. -/
def zeroIso (M : PModule.{u,0,w} R ℝ) : (shift 0).obj M ≅ M :=
  reindexIso (a := translation 0) (b := OrderHom.id) (fun t => add_zero t) M

/-- Composition of shifts is induced by associativity of addition of real indices. -/
def compIso (ε δ : ℝ≥0) (M : PModule.{u,0,w} R ℝ) :
    (shift ε).obj ((shift δ).obj M) ≅ (shift (ε + δ)).obj M :=
  reindexIso (a := (translation δ).comp (translation ε))
    (b := translation (ε + δ)) (fun t => by
      change (t + (ε : ℝ)) + (δ : ℝ) = t + ((ε : ℝ) + (δ : ℝ))
      exact add_assoc _ _ _) M

/-- The zero-shift component is the original module's map along index equality. -/
@[simp] theorem zeroIso_hom_app (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (zeroIso M).hom.app t = M.map (eqToHom (add_zero t)) := rfl

/-- The inverse zero-shift component transports along the reverse index equality. -/
@[simp] theorem zeroIso_inv_app (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (zeroIso M).inv.app t = M.map (eqToHom (add_zero t).symm) := rfl

/-- The composition component transports the actual translated index. -/
@[simp] theorem compIso_hom_app (ε δ : ℝ≥0) (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (compIso ε δ M).hom.app t =
      M.map (eqToHom (show (t + (ε : ℝ)) + (δ : ℝ) = t + ((ε + δ : ℝ≥0) : ℝ) by
        simp [add_assoc])) := rfl

/-- Zero-shift identification is natural in the module. -/
@[reassoc] theorem zeroIso_naturality {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    (shift 0).map f ≫ (zeroIso N).hom = (zeroIso M).hom ≫ f := by
  apply NatTrans.ext
  funext t
  exact (f.naturality (eqToHom (add_zero t))).symm

/-- Naturality of the inverse shift unit. -/
@[reassoc] theorem zeroIso_inv_naturality {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    (zeroIso M).inv ≫ (shift 0).map f = f ≫ (zeroIso N).inv := by
  apply NatTrans.ext
  funext t
  exact f.naturality (eqToHom (add_zero t).symm)

/-- Shift composition identification is natural in the module. -/
theorem compIso_naturality (ε δ : ℝ≥0) {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    (shift ε).map ((shift δ).map f) ≫ (compIso ε δ N).hom =
      (compIso ε δ M).hom ≫ (shift (ε + δ)).map f := by
  apply NatTrans.ext
  funext t
  exact (f.naturality _).symm

/-- Identify equal shift parameters, with no arbitrary choice of a comparison map. -/
def congrIso {ε δ : ℝ≥0} (h : ε = δ) (M : PModule.{u,0,w} R ℝ) :
    (shift ε).obj M ≅ (shift δ).obj M :=
  reindexIso (fun t => congrArg (fun a : ℝ≥0 => t + (a : ℝ)) h) M

/-- Equal-parameter transport is the actual map along equality of translated indices. -/
@[simp] theorem congrIso_hom_app {ε δ : ℝ≥0} (h : ε = δ)
    (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (congrIso h M).hom.app t =
      M.map (eqToHom (congrArg (fun a : ℝ≥0 => t + (a : ℝ)) h)) := rfl

/-- Reflexive parameter transport is the identity isomorphism. -/
@[simp] theorem congrIso_refl (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) :
    congrIso (rfl : ε = ε) M = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext t
  exact M.map_id _

/-- Left unit coherence, with the parameter equality transport displayed. -/
@[reassoc] theorem compIso_zero_left (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) :
    (compIso 0 ε M).hom ≫ (congrIso (zero_add ε) M).hom =
      (zeroIso ((shift ε).obj M)).hom := by
  apply NatTrans.ext
  funext t
  change M.map _ ≫ M.map _ = M.map _
  rw [← M.map_comp]
  congr 1

/-- Right unit coherence, with the parameter equality transport displayed. -/
theorem compIso_zero_right (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) :
    (compIso ε 0 M).hom ≫ (congrIso (add_zero ε) M).hom =
      (shift ε).map (zeroIso M).hom := by
  apply NatTrans.ext
  funext t
  change M.map _ ≫ M.map _ = M.map _
  rw [← M.map_comp]
  congr 1

/-- Both parenthesizations of three shifts induce the same map of real-indexed modules. -/
theorem compIso_assoc (ε δ γ : ℝ≥0) (M : PModule.{u,0,w} R ℝ) :
    (compIso ε δ ((shift γ).obj M)).hom ≫ (compIso (ε + δ) γ M).hom =
      (shift ε).map (compIso δ γ M).hom ≫ (compIso ε (δ + γ) M).hom ≫
        (congrIso (add_assoc ε δ γ).symm M).hom := by
  apply NatTrans.ext
  funext t
  change M.map _ ≫ M.map _ = M.map _ ≫ M.map _ ≫ M.map _
  erw [← M.map_comp, ← M.map_comp, ← M.map_comp]
  congr 1

/-- The transition is built from the original module's forward structure maps. -/
def transition (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) : M ⟶ (shift ε).obj M where
  app t := structureMap M (le_add_of_nonneg_right ε.coe_nonneg)
  naturality s t f := by
    change M.map f ≫ M.map _ = M.map _ ≫ M.map _
    rw [← M.map_comp, ← M.map_comp]
    congr 1

/-- Transition components are the actual structure maps from `t` to `t + ε`. -/
@[simp] theorem transition_app (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) (t : ℝ) :
    (transition ε M).app t = structureMap M (le_add_of_nonneg_right ε.coe_nonneg) := rfl

/-- Transitions commute with every natural transformation of modules. -/
theorem transition_naturality (ε : ℝ≥0) {M N : PModule.{u,0,w} R ℝ} (f : M ⟶ N) :
    f ≫ transition ε N = transition ε M ≫ (shift ε).map f := by
  apply NatTrans.ext
  funext t
  exact (f.naturality _).symm

/-- At zero, the transition followed by the canonical unit is the identity. -/
theorem transition_zero (M : PModule.{u,0,w} R ℝ) :
    transition 0 M ≫ (zeroIso M).hom = 𝟙 M := by
  apply NatTrans.ext
  funext t
  change M.map _ ≫ M.map _ = 𝟙 _
  erw [← M.map_comp]
  exact (congrArg M.map (Subsingleton.elim _ (𝟙 t))).trans (M.map_id t)

/-- The zero transition is exactly the inverse canonical shift unit. -/
theorem transition_zero_eq (M : PModule.{u,0,w} R ℝ) :
    transition 0 M = (zeroIso M).inv := by
  apply (cancel_mono (zeroIso M).hom).mp
  rw [transition_zero, Iso.inv_hom_id]

/-- Transition maps respect equal parameters through the canonical comparison. -/
theorem transition_congr {ε δ : ℝ≥0} (h : ε = δ) (M : PModule.{u,0,w} R ℝ) :
    transition ε M ≫ (congrIso h M).hom = transition δ M := by
  cases h
  simp only [congrIso_refl, Iso.refl_hom, Category.comp_id]

/-- Two actual transitions compose to the transition by the sum. -/
theorem transition_add (ε δ : ℝ≥0) (M : PModule.{u,0,w} R ℝ) :
    transition ε M ≫ (shift ε).map (transition δ M) ≫ (compIso ε δ M).hom =
      transition (ε + δ) M := by
  apply NatTrans.ext
  funext t
  change M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  erw [← M.map_comp, ← M.map_comp]
  congr 1

end RealShift

open RealShift

variable {R : Type u} [Ring R]

/-- A real epsilon-interleaving consists of actual natural maps and both double-shift
identities. The shift-composition comparison is the one constructed from real addition. -/
structure RealInterleaving (ε : ℝ≥0) (M N : PModule.{u,0,w} R ℝ) where
  /-- The map from the first module to the shifted second module. -/
  φ : M ⟶ (shift ε).obj N
  /-- The map from the second module to the shifted first module. -/
  ψ : N ⟶ (shift ε).obj M
  /-- The first composite is the actual double-shift structure map. -/
  φ_ψ : φ ≫ (shift ε).map ψ ≫ (compIso ε ε M).hom = transition (ε + ε) M
  /-- The second composite is the actual double-shift structure map. -/
  ψ_φ : ψ ≫ (shift ε).map φ ≫ (compIso ε ε N).hom = transition (ε + ε) N

namespace RealInterleaving

variable {ε : ℝ≥0} {M N : PModule.{u,0,w} R ℝ}

/-- Two witnesses agree when their two natural transformations agree. -/
@[ext] theorem ext {i j : RealInterleaving ε M N} (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) :
    i = j := by cases i; cases j; cases hφ; cases hψ; rfl

/-- Objectwise form of the first double-shift identity, including the index transport. -/
theorem φ_ψ_app (i : RealInterleaving ε M N) (t : ℝ) :
    i.φ.app t ≫ i.ψ.app (t + (ε : ℝ)) ≫ (compIso ε ε M).hom.app t =
      (transition (ε + ε) M).app t :=
  congrArg (fun f => f.app t) i.φ_ψ

/-- Objectwise form of the second double-shift identity, including the index transport. -/
theorem ψ_φ_app (i : RealInterleaving ε M N) (t : ℝ) :
    i.ψ.app t ≫ i.φ.app (t + (ε : ℝ)) ≫ (compIso ε ε N).hom.app t =
      (transition (ε + ε) N).app t :=
  congrArg (fun f => f.app t) i.ψ_φ

/-- The two transformation equations are equivalent to their component equations. -/
theorem equations_iff (f : M ⟶ (shift ε).obj N) (g : N ⟶ (shift ε).obj M) :
    (f ≫ (shift ε).map g ≫ (compIso ε ε M).hom = transition (ε + ε) M ∧
      g ≫ (shift ε).map f ≫ (compIso ε ε N).hom = transition (ε + ε) N) ↔
    (∀ t, f.app t ≫ g.app (t + (ε : ℝ)) ≫ (compIso ε ε M).hom.app t =
      (transition (ε + ε) M).app t) ∧
    (∀ t, g.app t ≫ f.app (t + (ε : ℝ)) ≫ (compIso ε ε N).hom.app t =
      (transition (ε + ε) N).app t) := by
  constructor
  · rintro ⟨hf, hg⟩
    exact ⟨fun t => congrArg (fun f => f.app t) hf,
      fun t => congrArg (fun f => f.app t) hg⟩
  · rintro ⟨hf, hg⟩
    constructor
    · apply NatTrans.ext; funext t; exact hf t
    · apply NatTrans.ext; funext t; exact hg t

/-- Construct a witness from actual natural maps and checked component identities. -/
def ofApp (f : M ⟶ (shift ε).obj N) (g : N ⟶ (shift ε).obj M)
    (hf : ∀ t, f.app t ≫ g.app (t + (ε : ℝ)) ≫ (compIso ε ε M).hom.app t =
      (transition (ε + ε) M).app t)
    (hg : ∀ t, g.app t ≫ f.app (t + (ε : ℝ)) ≫ (compIso ε ε N).hom.app t =
      (transition (ε + ε) N).app t) : RealInterleaving ε M N :=
  ⟨f, g, ((equations_iff f g).mpr ⟨hf, hg⟩).1, ((equations_iff f g).mpr ⟨hf, hg⟩).2⟩

/-- Interchange the two actual transformations. -/
def symm (i : RealInterleaving ε M N) : RealInterleaving ε N M :=
  ⟨i.ψ, i.φ, i.ψ_φ, i.φ_ψ⟩

/-- A module is interleaved with itself by its actual transition maps. -/
def refl (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) : RealInterleaving ε M M :=
  ⟨transition ε M, transition ε M, transition_add ε ε M, transition_add ε ε M⟩

/-- A natural isomorphism constructs a zero-interleaving using the canonical shift unit. -/
def ofIso (e : M ≅ N) : RealInterleaving 0 M N :=
  { φ := e.hom ≫ (zeroIso N).inv
    ψ := e.inv ≫ (zeroIso M).inv
    φ_ψ := by
      apply (cancel_mono (congrIso (zero_add 0) M).hom).mp
      simp only [Functor.map_comp, Category.assoc, compIso_zero_left,
        zeroIso_inv_naturality_assoc, e.hom_inv_id_assoc, Iso.inv_hom_id,
        Category.comp_id, transition_congr, transition_zero_eq]
    ψ_φ := by
      apply (cancel_mono (congrIso (zero_add 0) N).hom).mp
      simp only [Functor.map_comp, Category.assoc, compIso_zero_left,
        zeroIso_inv_naturality_assoc, e.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id, transition_congr, transition_zero_eq] }

/-- A zero-interleaving's two transformations give inverse natural transformations. -/
def toIso (i : RealInterleaving 0 M N) : M ≅ N where
  hom := i.φ ≫ (zeroIso N).hom
  inv := i.ψ ≫ (zeroIso M).hom
  hom_inv_id := by
    calc
      (i.φ ≫ (zeroIso N).hom) ≫ (i.ψ ≫ (zeroIso M).hom) =
          (i.φ ≫ (shift 0).map i.ψ ≫ (compIso 0 0 M).hom) ≫
            (congrIso (zero_add 0) M).hom ≫ (zeroIso M).hom := by
        simp only [Category.assoc, compIso_zero_left_assoc, zeroIso_naturality_assoc]
      _ = transition 0 M ≫ (zeroIso M).hom := by
        rw [i.φ_ψ, ← Category.assoc, transition_congr]
      _ = 𝟙 M := transition_zero M
  inv_hom_id := by
    calc
      (i.ψ ≫ (zeroIso M).hom) ≫ (i.φ ≫ (zeroIso N).hom) =
          (i.ψ ≫ (shift 0).map i.φ ≫ (compIso 0 0 N).hom) ≫
            (congrIso (zero_add 0) N).hom ≫ (zeroIso N).hom := by
        simp only [Category.assoc, compIso_zero_left_assoc, zeroIso_naturality_assoc]
      _ = transition 0 N ≫ (zeroIso N).hom := by
        rw [i.ψ_φ, ← Category.assoc, transition_congr]
      _ = 𝟙 N := transition_zero N

/-- Zero-interleaving witnesses and natural isomorphisms are equivalent as data. -/
def zeroEquivIso : RealInterleaving 0 M N ≃ (M ≅ N) where
  toFun := toIso
  invFun := ofIso
  left_inv i := by
    apply ext
    · change (i.φ ≫ (zeroIso N).hom) ≫ (zeroIso N).inv = i.φ
      simp [Category.assoc]
    · change (i.ψ ≫ (zeroIso M).hom) ≫ (zeroIso M).inv = i.ψ
      simp [Category.assoc]
  right_inv e := by
    apply Iso.ext
    change (e.hom ≫ (zeroIso N).inv) ≫ (zeroIso N).hom = e.hom
    simp [Category.assoc]

/-- The shifted zero module is zero, at every finite shift parameter. -/
theorem shift_isZero_zero (ε : ℝ≥0) :
    IsZero ((shift ε).obj (0 : PModule.{u,0,w} R ℝ)) := by
  apply Functor.isZero
  intro t
  exact Functor.zero_obj (t + (ε : ℝ))

/-- Interleaving with zero is exactly annihilation by the actual double-shift map. -/
theorem nonempty_zero_iff (ε : ℝ≥0) (M : PModule.{u,0,w} R ℝ) :
    Nonempty (RealInterleaving ε M 0) ↔ transition (ε + ε) M = 0 := by
  constructor
  · rintro ⟨i⟩
    have hφ : i.φ = 0 := (shift_isZero_zero ε).eq_of_tgt _ _
    rw [← i.φ_ψ, hφ, zero_comp]
  · intro h
    refine ⟨⟨0, 0, ?_, ?_⟩⟩
    · rw [zero_comp, h]
    · exact (isZero_zero (PModule.{u,0,w} R ℝ)).eq_of_src _ _

end RealInterleaving

end TDA.Persistence
