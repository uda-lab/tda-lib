import TDA.Persistence.CoordinateInterleavingDistance
import TDA.Persistence.RealInterleavingDistance

/-!
# The one-coordinate real line

Evaluation at the unique coordinate identifies `Fin 1 → ℝ` with `ℝ` as an
ordered index. Under this identification diagonal shifts, their comparison
maps, and interleaving witnesses agree with the real-indexed constructions.
-/

set_option autoImplicit false

universe u w

namespace TDA.Persistence

open CategoryTheory
open scoped TDA.Persistence NNReal ENNReal

namespace CoordinateRealBridge

variable {R : Type u} [Ring R]

/-- Evaluation at the sole coordinate is an order isomorphism. -/
def indexIso : (Fin 1 → ℝ) ≃o ℝ where
  toFun a := a 0
  invFun t := fun _ => t
  left_inv a := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl
  map_rel_iff' {a b} := by
    constructor
    · intro h i
      fin_cases i
      exact h
    · intro h
      exact h 0

/-- Evaluate the unique coordinate monotonically. -/
def evaluate : (Fin 1 → ℝ) →o ℝ where
  toFun a := a 0
  monotone' _ _ h := h 0

/-- Place a real number in the unique coordinate. -/
def diagonal : ℝ →o (Fin 1 → ℝ) where
  toFun t := fun _ => t
  monotone' _ _ h _ := h

@[simp] theorem evaluate_diagonal (t : ℝ) : evaluate (diagonal t) = t := rfl

@[simp] theorem diagonal_evaluate (a : Fin 1 → ℝ) : diagonal (evaluate a) = a :=
  indexIso.left_inv a

/-- Reindex a real persistence module on its single coordinate. -/
def fromReal (M : PModule.{u,0,w} R ℝ) : PModule.{u,0,w} R (Fin 1 → ℝ) :=
  reindex evaluate M

@[simp] theorem fromReal_obj (M : PModule.{u,0,w} R ℝ) (a : Fin 1 → ℝ) :
    (fromReal M).obj a = M.obj (a 0) := rfl

/-- A real interleaving gives an interleaving of the one-coordinate modules. -/
def toCoordinate {ε : ℝ≥0} {M N : PModule.{u,0,w} R ℝ}
    (i : RealInterleaving ε M N) :
    CoordinateInterleaving ε (fromReal M) (fromReal N) :=
  CoordinateInterleaving.ofApp
    (reindexNatTrans evaluate i.φ)
    (reindexNatTrans evaluate i.ψ)
    (fun a => by
      change i.φ.app (a 0) ≫ i.ψ.app (a 0 + (ε : ℝ)) ≫
        (RealShift.compIso ε ε M).hom.app (a 0) =
        (RealShift.transition (ε + ε) M).app (a 0)
      exact i.φ_ψ_app (a 0))
    (fun a => by
      change i.ψ.app (a 0) ≫ i.φ.app (a 0 + (ε : ℝ)) ≫
        (RealShift.compIso ε ε N).hom.app (a 0) =
        (RealShift.transition (ε + ε) N).app (a 0)
      exact i.ψ_φ_app (a 0))

/-- A one-coordinate interleaving evaluates to a real interleaving. -/
def toReal {ε : ℝ≥0} {M N : PModule.{u,0,w} R ℝ}
    (i : CoordinateInterleaving ε (fromReal M) (fromReal N)) :
    RealInterleaving ε M N :=
  RealInterleaving.ofApp
    (reindexNatTrans diagonal i.φ)
    (reindexNatTrans diagonal i.ψ)
    (fun t => by
      change i.φ.app (diagonal t) ≫
        i.ψ.app (CoordinateShift.translation ε (diagonal t)) ≫
        (CoordinateShift.compIso ε ε (fromReal M)).hom.app (diagonal t) =
        (CoordinateShift.transition (ε + ε) (fromReal M)).app (diagonal t)
      exact i.φ_ψ_app (diagonal t))
    (fun t => by
      change i.ψ.app (diagonal t) ≫
        i.φ.app (CoordinateShift.translation ε (diagonal t)) ≫
        (CoordinateShift.compIso ε ε (fromReal N)).hom.app (diagonal t) =
        (CoordinateShift.transition (ε + ε) (fromReal N)).app (diagonal t)
      exact i.ψ_φ_app (diagonal t))

/-- The conversions preserve the complete interleaving witness data. -/
def interleavingEquiv (ε : ℝ≥0) (M N : PModule.{u,0,w} R ℝ) :
    RealInterleaving ε M N ≃
      CoordinateInterleaving ε (fromReal M) (fromReal N) where
  toFun := toCoordinate
  invFun := toReal
  left_inv i := by
    apply RealInterleaving.ext
    · apply NatTrans.ext
      funext t
      rfl
    · apply NatTrans.ext
      funext t
      rfl
  right_inv i := by
    apply CoordinateInterleaving.ext
    · apply NatTrans.ext
      funext a
      change i.φ.app (diagonal (evaluate a)) = i.φ.app a
      congr 1
      exact diagonal_evaluate a
    · apply NatTrans.ext
      funext a
      change i.ψ.app (diagonal (evaluate a)) = i.ψ.app a
      congr 1
      exact diagonal_evaluate a

/-- Real and one-coordinate interleavings exist at precisely the same parameters. -/
theorem interleaving_nonempty_iff (ε : ℝ≥0)
    (M N : PModule.{u,0,w} R ℝ) :
    Nonempty (RealInterleaving ε M N) ↔
      Nonempty (CoordinateInterleaving ε (fromReal M) (fromReal N)) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨toCoordinate i⟩
  · rintro ⟨i⟩
    exact ⟨toReal i⟩

/-- The one-coordinate distance is the real interleaving distance. -/
theorem distance_eq (M N : PModule.{u,0,w} R ℝ) :
    coordinateInterleavingDistance (fromReal M) (fromReal N) =
      realInterleavingDistance M N := by
  apply le_antisymm
  · apply (le_realInterleavingDistance_iff).2
    intro ε h
    exact coordinateInterleavingDistance_le_of_nonempty
      ((interleaving_nonempty_iff ε M N).mp h)
  · apply (le_coordinateInterleavingDistance_iff).2
    intro ε h
    exact realInterleavingDistance_le_of_nonempty
      ((interleaving_nonempty_iff ε M N).mpr h)

end CoordinateRealBridge
end TDA.Persistence
