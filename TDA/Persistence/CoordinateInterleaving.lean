import TDA.Persistence.CoordinateShift

/-!
# Interleavings of real-coordinate persistence modules

Witnesses consist of natural transformations and both double-shift equations.
They work over a ring, at every finite nonnegative parameter, including on the
empty coordinate set. No finite-presentation or finite-dimensional hypothesis
is needed for these categorical operations.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory CoordinateShift
open scoped TDA.Persistence NNReal

variable {R : Type u} [Ring R] {n : ℕ}

/-- A diagonal interleaving with actual natural maps and both composite laws. -/
structure CoordinateInterleaving (ε : ℝ≥0)
    (M N : PModule.{u,0,w} R (Fin n → ℝ)) where
  /-- Forward map into the shifted second module. -/
  φ : M ⟶ (shift ε).obj N
  /-- Reverse map into the shifted first module. -/
  ψ : N ⟶ (shift ε).obj M
  /-- The first composite is the forward transition by twice the parameter. -/
  φ_ψ : φ ≫ (shift ε).map ψ ≫ (compIso ε ε M).hom = transition (ε + ε) M
  /-- The second composite is the other forward transition. -/
  ψ_φ : ψ ≫ (shift ε).map φ ≫ (compIso ε ε N).hom = transition (ε + ε) N

namespace CoordinateInterleaving

variable {ε δ σ : ℝ≥0}
  {M N P : PModule.{u,0,w} R (Fin n → ℝ)}

@[ext] theorem ext {i j : CoordinateInterleaving ε M N}
    (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) : i = j := by
  cases i; cases j; cases hφ; cases hψ; rfl

/-- First interleaving equation at a coordinate grade. -/
theorem φ_ψ_app (i : CoordinateInterleaving ε M N) (a : Fin n → ℝ) :
    i.φ.app a ≫ i.ψ.app (translation ε a) ≫ (compIso ε ε M).hom.app a =
      (transition (ε + ε) M).app a :=
  congrArg (fun f => f.app a) i.φ_ψ

/-- Second interleaving equation at a coordinate grade. -/
theorem ψ_φ_app (i : CoordinateInterleaving ε M N) (a : Fin n → ℝ) :
    i.ψ.app a ≫ i.φ.app (translation ε a) ≫ (compIso ε ε N).hom.app a =
      (transition (ε + ε) N).app a :=
  congrArg (fun f => f.app a) i.ψ_φ

/-- Equality of the two natural transformations is equivalent to equality at every grade. -/
theorem equations_iff (f : M ⟶ (shift ε).obj N) (g : N ⟶ (shift ε).obj M) :
    (f ≫ (shift ε).map g ≫ (compIso ε ε M).hom = transition (ε + ε) M ∧
      g ≫ (shift ε).map f ≫ (compIso ε ε N).hom = transition (ε + ε) N) ↔
    (∀ a, f.app a ≫ g.app (translation ε a) ≫ (compIso ε ε M).hom.app a =
      (transition (ε + ε) M).app a) ∧
    (∀ a, g.app a ≫ f.app (translation ε a) ≫ (compIso ε ε N).hom.app a =
      (transition (ε + ε) N).app a) := by
  constructor
  · rintro ⟨hf, hg⟩
    exact ⟨fun a => congrArg (fun x => x.app a) hf,
      fun a => congrArg (fun x => x.app a) hg⟩
  · rintro ⟨hf, hg⟩
    constructor
    · apply NatTrans.ext; funext a; exact hf a
    · apply NatTrans.ext; funext a; exact hg a

/-- Assemble an interleaving from natural maps and checked component equations. -/
def ofApp (f : M ⟶ (shift ε).obj N) (g : N ⟶ (shift ε).obj M)
    (hf : ∀ a, f.app a ≫ g.app (translation ε a) ≫ (compIso ε ε M).hom.app a =
      (transition (ε + ε) M).app a)
    (hg : ∀ a, g.app a ≫ f.app (translation ε a) ≫ (compIso ε ε N).hom.app a =
      (transition (ε + ε) N).app a) : CoordinateInterleaving ε M N :=
  ⟨f, g, ((equations_iff f g).mpr ⟨hf, hg⟩).1,
    ((equations_iff f g).mpr ⟨hf, hg⟩).2⟩

/-- Reverse the two natural transformations. -/
def symm (i : CoordinateInterleaving ε M N) : CoordinateInterleaving ε N M :=
  ⟨i.ψ, i.φ, i.ψ_φ, i.φ_ψ⟩

/-- A module interleaves with itself through its transition maps. -/
def refl (ε : ℝ≥0) (M : PModule.{u,0,w} R (Fin n → ℝ)) :
    CoordinateInterleaving ε M M :=
  ⟨transition ε M, transition ε M, transition_add ε ε M, transition_add ε ε M⟩

/-- A natural isomorphism yields a zero interleaving. -/
def ofIso (e : M ≅ N) : CoordinateInterleaving 0 M N :=
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

/-- A zero interleaving gives inverse natural transformations. -/
def toIso (i : CoordinateInterleaving 0 M N) : M ≅ N where
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

/-- Zero interleavings and natural isomorphisms are equivalent as data. -/
def zeroEquivIso : CoordinateInterleaving 0 M N ≃ (M ≅ N) where
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

/-- Every coordinate grade precedes its double nonnegative translate. -/
theorem twice_le (ε : ℝ≥0) (a : Fin n → ℝ) :
    a ≤ translation ε (translation ε a) := by
  intro j
  change a j ≤ (a j + (ε : ℝ)) + (ε : ℝ)
  exact (le_add_of_nonneg_right ε.coe_nonneg).trans
    (le_add_of_nonneg_right ε.coe_nonneg)

/-- The first equation before transporting the twice-shifted index. -/
@[reassoc] theorem φ_ψ_structureMap (i : CoordinateInterleaving ε M N)
    (a : Fin n → ℝ) :
    i.φ.app a ≫ i.ψ.app (translation ε a) = structureMap M (twice_le ε a) := by
  apply (cancel_mono ((compIso ε ε M).hom.app a)).mp
  erw [Category.assoc, i.φ_ψ_app]
  change M.map _ = M.map _ ≫ M.map _
  erw [← M.map_comp]
  congr 1

/-- Construct an interleaving from its two pointwise structure-map equations. -/
def ofStructureMapEquations (f : M ⟶ (shift ε).obj N)
    (g : N ⟶ (shift ε).obj M)
    (hf : ∀ a, f.app a ≫ g.app (translation ε a) = structureMap M (twice_le ε a))
    (hg : ∀ a, g.app a ≫ f.app (translation ε a) = structureMap N (twice_le ε a)) :
    CoordinateInterleaving ε M N :=
  ofApp f g (fun a => by
    erw [← Category.assoc, hf]
    change M.map _ ≫ M.map _ = M.map _
    erw [← M.map_comp]
    congr 1) (fun a => by
    erw [← Category.assoc, hg]
    change N.map _ ≫ N.map _ = N.map _
    erw [← N.map_comp]
    congr 1)

private theorem enlarge_equation (h : ε ≤ δ)
    (i : CoordinateInterleaving ε M N) (a : Fin n → ℝ) :
    (i.φ ≫ shiftLE h N).app a ≫
        (i.ψ ≫ shiftLE h M).app (translation δ a) =
      structureMap M (twice_le δ a) := by
  dsimp only [NatTrans.comp_app, shiftLE, shift, reindex]
  repeat' erw [Category.assoc]
  erw [i.ψ.naturality_assoc]
  erw [← Category.assoc, i.φ_ψ_structureMap]
  change M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  erw [← M.map_comp, ← M.map_comp]
  congr 1

/-- Enlarge an interleaving parameter using the original structure maps. -/
def mono (i : CoordinateInterleaving ε M N) (h : ε ≤ δ) :
    CoordinateInterleaving δ M N :=
  ofStructureMapEquations (i.φ ≫ shiftLE h N) (i.ψ ≫ shiftLE h M)
    (enlarge_equation h i) (enlarge_equation h i.symm)

private def composeMap (f : M ⟶ (shift ε).obj N)
    (g : N ⟶ (shift δ).obj P) (h : ε + δ = σ) :
    M ⟶ (shift σ).obj P :=
  f ≫ (shift ε).map g ≫ (compIso ε δ P).hom ≫ (congrIso h P).hom

private theorem compose_equation (i : CoordinateInterleaving ε M N)
    (j : CoordinateInterleaving δ N P) (h : ε + δ = σ)
    (h' : δ + ε = σ) (a : Fin n → ℝ) :
    (composeMap i.φ j.φ h).app a ≫
        (composeMap j.ψ i.ψ h').app (translation σ a) =
      structureMap M (twice_le σ a) := by
  dsimp only [composeMap, NatTrans.comp_app, shift_map_app]
  simp only [compIso_hom_app, congrIso_hom_app]
  repeat' erw [Category.assoc]
  -- Move index equalities through natural transformations before cancelling.
  erw [j.ψ.naturality_assoc]
  erw [j.ψ.naturality_assoc]
  erw [i.ψ.naturality_assoc]
  erw [i.ψ.naturality_assoc]
  erw [← Category.assoc (j.φ.app (translation ε a))
    (j.ψ.app (translation δ (translation ε a))), j.φ_ψ_structureMap]
  erw [i.ψ.naturality_assoc]
  erw [← Category.assoc (i.φ.app a) (i.ψ.app (translation ε a)),
    i.φ_ψ_structureMap]
  change M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ ≫ M.map _ = M.map _
  repeat' erw [← M.map_comp]
  congr 1

/-- Compose interleavings and add their parameters. -/
def trans (i : CoordinateInterleaving ε M N)
    (j : CoordinateInterleaving δ N P) :
    CoordinateInterleaving (ε + δ) M P :=
  ofStructureMapEquations (composeMap i.φ j.φ rfl)
    (composeMap j.ψ i.ψ (add_comm δ ε))
    (compose_equation i j rfl (add_comm δ ε))
    (compose_equation j.symm i.symm (add_comm δ ε) rfl)

/-- Transport both modules along natural isomorphisms. -/
def congr {M' N' : PModule.{u,0,w} R (Fin n → ℝ)}
    (i : CoordinateInterleaving ε M N) (e : M ≅ M') (d : N ≅ N') :
    CoordinateInterleaving ε M' N' := by
  have comp {A B A' B' : PModule.{u,0,w} R (Fin n → ℝ)}
      (f : A ⟶ (shift ε).obj B) (g : B ⟶ (shift ε).obj A)
      (h : f ≫ (shift ε).map g ≫ (compIso ε ε A).hom = transition (ε + ε) A)
      (a : A ≅ A') (b : B ≅ B') :
      (a.inv ≫ f ≫ (shift ε).map b.hom) ≫
        (shift ε).map (b.inv ≫ g ≫ (shift ε).map a.hom) ≫
          (compIso ε ε A').hom = transition (ε + ε) A' := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, b.hom_inv_id, (shift ε).map_id, Category.id_comp]
    rw [compIso_naturality]
    have hh := congrArg (fun m => a.inv ≫ m ≫ (shift (ε + ε)).map a.hom) h
    simp only [Category.assoc] at hh
    rw [hh]
    rw [← transition_naturality, Iso.inv_hom_id_assoc]
  exact ⟨e.inv ≫ i.φ ≫ (shift ε).map d.hom,
    d.inv ≫ i.ψ ≫ (shift ε).map e.hom,
    comp i.φ i.ψ i.φ_ψ e d, comp i.ψ i.φ i.ψ_φ d e⟩

end CoordinateInterleaving
end TDA.Persistence
