import TDA.Persistence.Reduction.FiniteInputImage
import TDA.Persistence.Reduction.FiniteInputHomologyDimensionsCorrectness
import TDA.Persistence.RankInvariant

/-!
# Computed ranks for sampled image persistence

The table stores every forward cross-stage rank once. Its integer extension
uses zero outside the finite observation triangle; the sentinel indices do not
add observations. All executable definitions use the existing finite F₂ rank
evaluator. The actual image module occurs only in correctness statements.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open CategoryTheory

variable {N : ℕ}

/-- Geometry, global grade preservation, and the order of the supplied observations. -/
def ImageBarcodeInput (xs ys : Input) (f : ℕ → ℕ) (t : Fin N → ℤ) : Prop :=
  GlobalVertexMapInput xs ys f ∧ Monotone t

instance (xs ys : Input) (f : ℕ → ℕ) (t : Fin N → ℤ) :
    Decidable (ImageBarcodeInput xs ys f t) := by
  unfold ImageBarcodeInput Monotone
  infer_instance

/-- Materialized square storage; entries below the forward triangle are zero. -/
abbrev ImageRankTable (N : ℕ) := Vector (Vector ℕ N) N

/-- Every comparable pair uses the actual cross-threshold rank evaluator. -/
def imageRankTable (xs ys : Input) (p : ℕ) (f : ℕ → ℕ) (t : Fin N → ℤ) :
    ImageRankTable N :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    if i ≤ j then (homologyMapDimensions xs ys p (t i) (t j) f).rank else 0

/-- Access one stored rank. -/
def imageRank (R : ImageRankTable N) (i j : Fin N) : ℕ := R[i.val][j.val]

@[simp] theorem imageRank_table (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (i j : Fin N) (hij : i ≤ j) :
    imageRank (imageRankTable xs ys p f t) i j =
      (homologyMapDimensions xs ys p (t i) (t j) f).rank := by
  simp [imageRank, imageRankTable, hij]

/-- Signed extension of the stored table, with zero on all invalid integer pairs. -/
def imageRankInteger (R : ImageRankTable N) (i j : ℤ) : ℤ :=
  if h : 0 ≤ i ∧ i ≤ j ∧ j < (N : ℤ) then
    imageRank R ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩
  else 0

/-- Four-term difference in integers: subtraction occurs after the endpoint casts. -/
def imageMultiplicityInteger (R : ImageRankTable N) (b d : ℕ) : ℤ :=
  imageRankInteger R (b : ℤ) ((d : ℤ) - 1) -
  imageRankInteger R ((b : ℤ) - 1) ((d : ℤ) - 1) -
  imageRankInteger R (b : ℤ) (d : ℤ) +
  imageRankInteger R ((b : ℤ) - 1) (d : ℤ)

/-- The semantic image of the same validated observations and vertex function. -/
noncomputable def sampledImage (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t) : PModule (ZMod 2) (Fin N) :=
  finiteImage (sampledHomologyMap xs ys h.1.1 h.1.2.1 f h.1.2.2 p ⟨t, h.2⟩)

instance sampledImage_finiteDimensional (xs ys : Input) (p : ℕ) (f : ℕ → ℕ) (t : Fin N → ℤ)
    (h : ImageBarcodeInput xs ys f t) (i : Fin N) :
    FiniteDimensional (ZMod 2) ((sampledImage xs ys p f t h).obj i) := by
  unfold sampledImage
  infer_instance

/-- Stored ranks are structure-map ranks of the actual sampled image module. -/
theorem imageRank_correct (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t)
    (i j : Fin N) (hij : i ≤ j) :
    imageRank (imageRankTable xs ys p f t) i j =
      structureMapRank (sampledImage xs ys p f t h) i j hij := by
  rw [imageRank_table xs ys p f t i j hij]
  change _ = structureMapRank (finiteImage
    (sampledHomologyMap xs ys h.1.1 h.1.2.1 f h.1.2.2 p ⟨t, h.2⟩)) i j hij
  rw [sampledHomologyMap_image_rank]
  exact homologyMapDimensions_rank_actual xs ys h.1.1 h.1.2.1 p (t i) (t j) f
    (h.1.2.2.cross xs ys f (t i) (t j) (h.2 hij))

/-- The table measures the range of the actual simplicial map across thresholds. -/
theorem imageRank_actual (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t)
    (i j : Fin N) (hij : i ≤ j) :
    imageRank (imageRankTable xs ys p f t) i j =
      Module.finrank (ZMod 2) (LinearMap.range
        (TDA.Simplicial.simplicialHomologyMap (ZMod 2)
          (validatedVertexMap xs ys h.1.1 h.1.2.1 (t i) (t j) f
            (h.1.2.2.cross xs ys f (t i) (t j) (h.2 hij))) p).hom) := by
  rw [imageRank_table xs ys p f t i j hij]
  exact homologyMapDimensions_rank_actual xs ys h.1.1 h.1.2.1 p (t i) (t j) f _

/-- Integer correctness includes every sentinel and every invalid pair. -/
theorem imageRankInteger_correct (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t) (i j : ℤ) :
    imageRankInteger (imageRankTable xs ys p f t) i j =
      moduleRankInteger (sampledImage xs ys p f t h) i j := by
  unfold imageRankInteger moduleRankInteger
  split_ifs with hv
  · dsimp only
    exact congrArg (fun n : ℕ => (n : ℤ)) (imageRank_correct xs ys p f t h
      ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩ (by
        change i.toNat ≤ j.toNat
        omega))
  · rfl

/-- The computed signed difference is the module's multiplicity. -/
theorem imageMultiplicityInteger_correct (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t) (b d : ℕ) :
    imageMultiplicityInteger (imageRankTable xs ys p f t) b d =
      moduleMultiplicityInteger (sampledImage xs ys p f t h) b d := by
  simp only [imageMultiplicityInteger, moduleMultiplicityInteger, imageRankInteger_correct xs ys p f t h]

/-- Nonnegativity is proved before interpreting the difference as a multiplicity.
This includes birth zero and death at the observation count. -/
theorem imageMultiplicityInteger_nonneg (xs ys : Input) (p : ℕ) (f : ℕ → ℕ)
    (t : Fin N → ℤ) (h : ImageBarcodeInput xs ys f t) (b d : ℕ)
    (hbd : b < d) (hd : d ≤ N) :
    0 ≤ imageMultiplicityInteger (imageRankTable xs ys p f t) b d := by
  rw [imageMultiplicityInteger_correct xs ys p f t h]
  exact moduleMultiplicityInteger_nonneg _ b d hbd hd

end TDA.Persistence.Reduction.FiniteInput
