import TDA.Persistence.FiniteImageRank
import TDA.Persistence.Simplicial
import TDA.Persistence.Reduction.FiniteInputVertexMap

/-!
# Image persistence from finite graded simplicial input

The finite face-grade check uses one fixed ambient vertex function, in every
face degree. It is equivalent to preservation of all integer sublevels. The
sampled natural transformation uses the existing signed simplicial homology
maps over F₂, including collapsed faces. Its image ranks are the ranks of the
actual maps from a source sublevel to a later target sublevel.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration CategoryTheory

/-- Every source face has its image in the target at no later grade. -/
def GlobalVertexMapCondition (xs ys : Input) (f : ℕ → ℕ) : Prop :=
  ∀ i : Fin xs.length, ∃ j : Fin ys.length,
    (ys.get j).1 = (xs.get i).1.image f ∧ (ys.get j).2 ≤ (xs.get i).2

instance (xs ys : Input) (f : ℕ → ℕ) : Decidable (GlobalVertexMapCondition xs ys f) := by
  unfold GlobalVertexMapCondition
  infer_instance

/-- Global grade preservation together with both existing geometry validators. -/
def GlobalVertexMapInput (xs ys : Input) (f : ℕ → ℕ) : Prop :=
  Valid xs ∧ Valid ys ∧ GlobalVertexMapCondition xs ys f

instance (xs ys : Input) (f : ℕ → ℕ) : Decidable (GlobalVertexMapInput xs ys f) := by
  unfold GlobalVertexMapInput
  infer_instance

/-- Executable, bounded global validation, including all input geometry. -/
def validateGlobalVertexMap (xs ys : Input) (f : ℕ → ℕ) : Bool :=
  decide (GlobalVertexMapInput xs ys f)

@[simp] theorem validateGlobalVertexMap_eq_true (xs ys : Input) (f : ℕ → ℕ) :
    validateGlobalVertexMap xs ys f = true ↔ GlobalVertexMapInput xs ys f := by
  simp [validateGlobalVertexMap]

/-- Testing each occurrence at its own grade is equivalent to testing every sublevel. -/
theorem globalVertexMapCondition_iff (xs ys : Input) (f : ℕ → ℕ) :
    GlobalVertexMapCondition xs ys f ↔ ∀ a : ℤ, VertexMapCondition xs ys a a f := by
  constructor
  · intro h a i hi
    obtain ⟨j, hj, hg⟩ := h i
    exact ⟨j, hj, hg.trans hi⟩
  · intro h i
    exact h (xs.get i).2 i le_rfl

/-- Full global validation is equivalent to full validation at every integer threshold. -/
theorem globalVertexMapInput_iff (xs ys : Input) (f : ℕ → ℕ) :
    GlobalVertexMapInput xs ys f ↔ ∀ a : ℤ, VertexMapInput xs ys a a f := by
  constructor
  · rintro ⟨hx, hy, h⟩ a
    exact ⟨hx, hy, (globalVertexMapCondition_iff xs ys f).mp h a⟩
  · intro h
    exact ⟨(h 0).1, (h 0).2.1,
      (globalVertexMapCondition_iff xs ys f).mpr (fun a => (h a).2.2)⟩

/-- Global preservation supplies every forward cross-threshold face condition. -/
theorem GlobalVertexMapCondition.cross (xs ys : Input) (f : ℕ → ℕ)
    (h : GlobalVertexMapCondition xs ys f) (a b : ℤ) (hab : a ≤ b) :
    VertexMapCondition xs ys a b f := by
  intro i hi
  obtain ⟨j, hj, hg⟩ := h i
  exact ⟨j, hj, hg.trans (hi.trans hab)⟩

theorem globalVertexMapCondition_id (xs : Input) : GlobalVertexMapCondition xs xs id := by
  intro i
  exact ⟨i, by simp, le_rfl⟩

/-- Actual sublevel homology sampled at any monotone finite list of thresholds. -/
noncomputable def sampledHomology (xs : Input) (hx : Valid xs) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) : PModule (ZMod 2) (Fin s) :=
  reindex t (simplicialHomologyPModule (ZMod 2) (gradeFilter xs hx).sublevelFiltration p)

instance sampledHomology_finiteDimensional (xs : Input) (hx : Valid xs) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) (i : Fin s) :
    FiniteDimensional (ZMod 2) ((sampledHomology xs hx p t).obj i) :=
  (sublevelCoordinates xs hx p (t i)).symm.finiteDimensional

/-- A single globally preserving function induces the actual natural transformation. -/
noncomputable def sampledHomologyMap (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (f : ℕ → ℕ) (h : GlobalVertexMapCondition xs ys f) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) : sampledHomology xs hx p t ⟶ sampledHomology ys hy p t where
  app i := simplicialHomologyMap (ZMod 2)
    (validatedVertexMap xs ys hx hy (t i) (t i) f (h.cross xs ys f (t i) (t i) le_rfl)) p
  naturality {i j} g := by
    change simplicialHomologyIncl (ZMod 2)
        ((gradeFilter xs hx).sublevel_mono (t.monotone (leOfHom g))) p ≫
        simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy (t j) (t j) f
          (h.cross xs ys f (t j) (t j) le_rfl)) p =
      simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy (t i) (t i) f
        (h.cross xs ys f (t i) (t i) le_rfl)) p ≫
        simplicialHomologyIncl (ZMod 2)
          ((gradeFilter ys hy).sublevel_mono (t.monotone (leOfHom g))) p
    rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_inclusion,
      ← simplicialHomologyMap_comp, ← simplicialHomologyMap_comp]
    exact congrArg (fun q => simplicialHomologyMap (ZMod 2) q p) (VertexMap.ext (fun _ => rfl))

/-- The sampled component is the validated simplicial homology map. -/
@[simp] theorem sampledHomologyMap_app (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (f : ℕ → ℕ) (h : GlobalVertexMapCondition xs ys f) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) (i : Fin s) :
    (sampledHomologyMap xs ys hx hy f h p t).app i =
      simplicialHomologyMap (ZMod 2)
        (validatedVertexMap xs ys hx hy (t i) (t i) f (h.cross xs ys f (t i) (t i) le_rfl)) p := rfl

/-- Sampled structure maps are the existing actual sublevel inclusions. -/
theorem sampledHomology_structureMap (xs : Input) (hx : Valid xs) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) {i j : Fin s} (hij : i ≤ j) :
    structureMap (sampledHomology xs hx p t) hij =
      simplicialHomologyIncl (ZMod 2) ((gradeFilter xs hx).sublevel_mono (t.monotone hij)) p := rfl

/-- Naturality is with respect to the actual source and target inclusions. -/
theorem sampledHomologyMap_naturality (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (f : ℕ → ℕ) (h : GlobalVertexMapCondition xs ys f) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) {i j : Fin s} (hij : i ≤ j) :
    simplicialHomologyIncl (ZMod 2) ((gradeFilter xs hx).sublevel_mono (t.monotone hij)) p ≫
        (sampledHomologyMap xs ys hx hy f h p t).app j =
      (sampledHomologyMap xs ys hx hy f h p t).app i ≫
        simplicialHomologyIncl (ZMod 2) ((gradeFilter ys hy).sublevel_mono (t.monotone hij)) p :=
  (sampledHomologyMap xs ys hx hy f h p t).naturality (homOfLE hij)

/-- A component followed by a target inclusion is the same function across thresholds. -/
theorem sampledHomologyMap_cross (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (f : ℕ → ℕ) (h : GlobalVertexMapCondition xs ys f) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) {i j : Fin s} (hij : i ≤ j) :
    (sampledHomologyMap xs ys hx hy f h p t).app i ≫
        structureMap (sampledHomology ys hy p t) hij =
      simplicialHomologyMap (ZMod 2)
        (validatedVertexMap xs ys hx hy (t i) (t j) f
          (h.cross xs ys f (t i) (t j) (t.monotone hij))) p := by
  change simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy (t i) (t i) f
      (h.cross xs ys f (t i) (t i) le_rfl)) p ≫
      simplicialHomologyIncl (ZMod 2) ((gradeFilter ys hy).sublevel_mono (t.monotone hij)) p = _
  rw [← simplicialHomologyMap_inclusion, ← simplicialHomologyMap_comp]
  exact congrArg (fun q => simplicialHomologyMap (ZMod 2) q p) (VertexMap.ext (fun _ => rfl))

/-- The image rank is the range dimension of the actual cross-threshold simplicial map. -/
theorem sampledHomologyMap_image_rank (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (f : ℕ → ℕ) (h : GlobalVertexMapCondition xs ys f) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) (i j : Fin s) (hij : i ≤ j) :
    structureMapRank (finiteImage (sampledHomologyMap xs ys hx hy f h p t)) i j hij =
      Module.finrank (ZMod 2) (LinearMap.range
        (simplicialHomologyMap (ZMod 2)
          (validatedVertexMap xs ys hx hy (t i) (t j) f
            (h.cross xs ys f (t i) (t j) (t.monotone hij))) p).hom) := by
  rw [finiteImage_structureMapRank]
  change Module.finrank (ZMod 2) (LinearMap.range
    ((sampledHomologyMap xs ys hx hy f h p t).app i ≫
      structureMap (sampledHomology ys hy p t) hij).hom) = _
  rw [sampledHomologyMap_cross]
  rfl

/-- Identity vertex functions induce the identity sampled transformation. -/
@[simp] theorem sampledHomologyMap_id (xs : Input) (hx : Valid xs) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) :
    sampledHomologyMap xs xs hx hx id (globalVertexMapCondition_id xs) p t =
      𝟙 (sampledHomology xs hx p t) := by
  apply NatTrans.ext
  funext i
  rw [sampledHomologyMap_app]
  have he : validatedVertexMap xs xs hx hx (t i) (t i) id
      ((globalVertexMapCondition_id xs).cross xs xs id (t i) (t i) le_rfl) =
      VertexMap.id ((gradeFilter xs hx).sublevel (t i)) := by ext; rfl
  rw [he, simplicialHomologyMap_id]
  rfl

/-- The identity specialization recovers the ordinary sampled source rank. -/
@[simp] theorem sampledHomologyMap_id_image_rank (xs : Input) (hx : Valid xs) (p : ℕ)
    {s : ℕ} (t : Fin s →o ℤ) (i j : Fin s) (hij : i ≤ j) :
    structureMapRank (finiteImage
      (sampledHomologyMap xs xs hx hx id (globalVertexMapCondition_id xs) p t)) i j hij =
      structureMapRank (sampledHomology xs hx p t) i j hij := by
  rw [sampledHomologyMap_id, finiteImage_id_structureMapRank]

end TDA.Persistence.Reduction.FiniteInput
