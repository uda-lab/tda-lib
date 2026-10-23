import TDA.Persistence.QTame
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Persistence measures on separated rectangles

For `a ≤ b < c ≤ d`, the rectangle value is the dimension of
`(im(b → c) ∩ ker(c → d)) / (im(a → c) ∩ ker(c → d))`.
The denominator is viewed as a subspace of the numerator. Thus the construction only
requires finite-dimensional images across strict inequalities, and permits infinite fibers.

The rectangle-boundary convention is the one in Chazal–de Silva–Glisse–Oudot,
*The structure and stability of persistence modules*, arXiv:1207.3674v3, §2.1:
an interval contributes when it contains `b,c` and excludes `a,d`. Endpoint decorations
therefore matter; no uniform half-open convention is imposed on the module.
-/

universe u w

namespace TDA.Persistence

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- The image of a structure map, without a finite-dimensional fiber assumption. -/
def persistenceImage {a b : ℝ} (hab : a ≤ b) : Submodule k (M.obj b) :=
  LinearMap.range (structureMapLinear M hab)

/-- Classes present at `c`, born no later than `b`, and killed by `d`. -/
def persistenceKernel {b c d : ℝ} (hbc : b ≤ c) (hcd : c ≤ d) :
    Submodule k (M.obj c) :=
  persistenceImage M hbc ⊓ LinearMap.ker (structureMapLinear M hcd)

/-- Earlier images are contained in later images at a common target. -/
theorem persistenceImage_mono {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    persistenceImage M (hab.trans hbc) ≤ persistenceImage M hbc := by
  unfold persistenceImage
  rw [structureMapLinear_comp M hab hbc]
  exact LinearMap.range_comp_le_range _ _

/-- The earlier born-and-killed subspace is contained in the later one. -/
theorem persistenceKernel_mono {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    persistenceKernel M (hab.trans hbc) hcd ≤ persistenceKernel M hbc hcd :=
  inf_le_inf_right _ (persistenceImage_mono M hab hbc)

/-- The image quotient defining the persistence measure on `[a,b] × [c,d]`.
The boundary convention is expressed intrinsically by the four structure maps. -/
abbrev PersistenceMeasureSpace {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :=
  persistenceKernel M hbc hcd ⧸
    (persistenceKernel M (hab.trans hbc) hcd).comap
      (persistenceKernel M hbc hcd).subtype

/-- Dimension of the actual image quotient; its use as a finite measure is justified
by finite-dimensionality of the crossing image, not of the module's fibers. -/
noncomputable def persistenceMeasureValue {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : ℕ :=
  Module.finrank k (PersistenceMeasureSpace M hab hbc hcd)

private theorem image_restricted_range {b c d : ℝ} (hbc : b ≤ c) (hcd : c ≤ d) :
    LinearMap.range ((structureMapLinear M hcd).comp
      (persistenceImage M hbc).subtype) = persistenceImage M (hbc.trans hcd) := by
  unfold persistenceImage
  rw [structureMapLinear_comp M hbc hcd,
    LinearMap.range_comp, Submodule.range_subtype]
  exact (LinearMap.range_comp (structureMapLinear M hbc)
    (structureMapLinear M hcd)).symm

private theorem restricted_kernel_finrank {c d : ℝ} (hcd : c ≤ d)
    (U : Submodule k (M.obj c)) :
    Module.finrank k (LinearMap.ker ((structureMapLinear M hcd).comp U.subtype)) =
      Module.finrank k (U ⊓ LinearMap.ker (structureMapLinear M hcd) :
        Submodule k (M.obj c)) := by
  rw [← Submodule.finrank_map_subtype_eq U
    (LinearMap.ker ((structureMapLinear M hcd).comp U.subtype))]
  change Module.finrank k (Submodule.map U.subtype
    (LinearMap.ker ((structureMapLinear M hcd).domRestrict U))) = _
  rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]

/-- Rank-nullity within an image, valid even when the ambient fibers are infinite. -/
theorem persistenceImage_finrank_drop {b c d : ℝ} (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    Module.finrank k (persistenceImage M hbc) =
      Module.finrank k (persistenceImage M (hbc.trans hcd)) +
        Module.finrank k (persistenceKernel M hbc hcd) := by
  have h := LinearMap.finrank_range_add_finrank_ker
    ((structureMapLinear M hcd).comp (persistenceImage M hbc).subtype)
  rw [image_restricted_range M hbc hcd, restricted_kernel_finrank M hcd] at h
  exact h.symm

/-- A finite crossing image makes the image quotient finite-dimensional. -/
theorem persistenceMeasureSpace_finiteDimensional {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    FiniteDimensional k (PersistenceMeasureSpace M hab hbc hcd) := by
  have : FiniteDimensional k (persistenceKernel M hbc hcd) :=
    Submodule.finiteDimensional_of_le inf_le_left
  infer_instance

/-- Q-tameness supplies local finiteness on every rectangle separated from the diagonal. -/
theorem PModule.QTame.persistenceMeasureSpace_finiteDimensional
    (hM : M.QTame) {a b c d : ℝ} (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) :
    FiniteDimensional k (PersistenceMeasureSpace M hab hbc.le hcd) := by
  have : FiniteDimensional k (persistenceImage M hbc.le) := hM b c hbc
  exact TDA.Persistence.persistenceMeasureSpace_finiteDimensional M hab hbc.le hcd

/-- The measure plus the earlier born-and-killed dimension is the later dimension. -/
theorem persistenceMeasureValue_add_kernel {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceMeasureValue M hab hbc hcd +
      Module.finrank k (persistenceKernel M (hab.trans hbc) hcd) =
        Module.finrank k (persistenceKernel M hbc hcd) := by
  have : FiniteDimensional k (persistenceKernel M hbc hcd) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have h := Submodule.finrank_quotient_add_finrank
    ((persistenceKernel M (hab.trans hbc) hcd).comap
      (persistenceKernel M hbc hcd).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe
    (persistenceKernel_mono M hab hbc hcd)).finrank_eq] at h
  exact h

/-- Four-rank formula for the persistence measure. Only the crossing image must be finite. -/
theorem persistenceMeasureValue_four_rank {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    (persistenceMeasureValue M hab hbc hcd : ℤ) =
      Module.finrank k (persistenceImage M hbc) -
        Module.finrank k (persistenceImage M (hab.trans hbc)) -
        Module.finrank k (persistenceImage M (hbc.trans hcd)) +
        Module.finrank k (persistenceImage M ((hab.trans hbc).trans hcd)) := by
  have : FiniteDimensional k (persistenceImage M (hab.trans hbc)) :=
    Submodule.finiteDimensional_of_le (persistenceImage_mono M hab hbc)
  have h₁ := persistenceImage_finrank_drop M hbc hcd
  have h₂ := persistenceImage_finrank_drop M (hab.trans hbc) hcd
  have h₃ := persistenceMeasureValue_add_kernel M hab hbc hcd
  omega

/-- A later target retains finite-dimensionality of an already finite image. -/
theorem persistenceImage_finiteDimensional_target {b c d : ℝ}
    (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    FiniteDimensional k (persistenceImage M (hbc.trans hcd)) := by
  rw [← image_restricted_range M hbc hcd]
  infer_instance

/-- Finite additivity when splitting the birth coordinate. The shared boundary is handled
by the intermediate image, so its contributions cancel exactly. -/
theorem persistenceMeasureValue_split_birth {a x b c d : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceMeasureValue M (hax.trans hxb) hbc hcd =
      persistenceMeasureValue M hax (hxb.trans hbc) hcd +
        persistenceMeasureValue M hxb hbc hcd := by
  have : FiniteDimensional k (persistenceImage M (hxb.trans hbc)) :=
    Submodule.finiteDimensional_of_le (persistenceImage_mono M hxb hbc)
  have h := persistenceMeasureValue_four_rank M (hax.trans hxb) hbc hcd
  have h₁ := persistenceMeasureValue_four_rank M hax (hxb.trans hbc) hcd
  have h₂ := persistenceMeasureValue_four_rank M hxb hbc hcd
  omega

/-- Finite additivity when splitting the death coordinate. -/
theorem persistenceMeasureValue_split_death {a b c y d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcy : c ≤ y) (hyd : y ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceMeasureValue M hab hbc (hcy.trans hyd) =
      persistenceMeasureValue M hab hbc hcy +
        persistenceMeasureValue M hab (hbc.trans hcy) hyd := by
  have : FiniteDimensional k (persistenceImage M (hbc.trans hcy)) :=
    persistenceImage_finiteDimensional_target M hbc hcy
  have h := persistenceMeasureValue_four_rank M hab hbc (hcy.trans hyd)
  have h₁ := persistenceMeasureValue_four_rank M hab hbc hcy
  have h₂ := persistenceMeasureValue_four_rank M hab (hbc.trans hcy) hyd
  omega

/-- Every rectangle count is bounded by its finite crossing rank. -/
theorem persistenceMeasureValue_le_crossing_rank {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceMeasureValue M hab hbc hcd ≤ Module.finrank k (persistenceImage M hbc) := by
  have h₁ := persistenceMeasureValue_add_kernel M hab hbc hcd
  have h₂ := persistenceImage_finrank_drop M hbc hcd
  omega

/-- Restricting either coordinate of a rectangle cannot increase its measure. -/
theorem persistenceMeasureValue_mono {a a' b' b c c' d' d : ℝ}
    (haa : a ≤ a') (hab : a' ≤ b') (hbb : b' ≤ b) (hbc : b ≤ c)
    (hcc : c ≤ c') (hcd : c' ≤ d') (hdd : d' ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceMeasureValue M hab ((hbb.trans hbc).trans hcc) hcd ≤
      persistenceMeasureValue M ((haa.trans hab).trans hbb) hbc
        ((hcc.trans hcd).trans hdd) := by
  have : FiniteDimensional k (persistenceImage M (hbb.trans hbc)) :=
    Submodule.finiteDimensional_of_le (persistenceImage_mono M hbb hbc)
  have : FiniteDimensional k (persistenceImage M ((hbb.trans hbc).trans hcc)) :=
    persistenceImage_finiteDimensional_target M (hbb.trans hbc) hcc
  have h₁ := persistenceMeasureValue_split_birth M (haa.trans hab) hbb hbc
    ((hcc.trans hcd).trans hdd)
  have h₂ := persistenceMeasureValue_split_birth M haa hab (hbb.trans hbc)
    ((hcc.trans hcd).trans hdd)
  have h₃ := persistenceMeasureValue_split_death M hab (hbb.trans hbc) hcc
    (hcd.trans hdd)
  have h₄ := persistenceMeasureValue_split_death M hab ((hbb.trans hbc).trans hcc)
    hcd hdd
  omega

/-- A zero crossing map carries no rectangle mass. In particular ephemeral information
cannot be recovered from separated persistence rectangles. -/
theorem persistenceMeasureValue_eq_zero_of_crossing_eq_zero {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hzero : structureMapLinear M hbc = 0) :
    persistenceMeasureValue M hab hbc hcd = 0 := by
  have h : persistenceKernel M hbc hcd = ⊥ := by
    simp [persistenceKernel, persistenceImage, hzero]
  unfold persistenceMeasureValue PersistenceMeasureSpace
  rw [h]
  exact Module.finrank_eq_zero_of_subsingleton k _

/-- A degenerate birth strip carries no measure. -/
@[simp] theorem persistenceMeasureValue_birth_self {a c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) :
    persistenceMeasureValue M (le_refl a) hac hcd = 0 := by
  change Module.finrank k (persistenceKernel M hac hcd ⧸
    (persistenceKernel M hac hcd).comap (persistenceKernel M hac hcd).subtype) = 0
  rw [Submodule.comap_subtype_self]
  exact Module.finrank_eq_zero_of_subsingleton k _

/-- A degenerate death strip carries no measure. -/
@[simp] theorem persistenceMeasureValue_death_self {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    persistenceMeasureValue M hab hbc (le_refl c) = 0 := by
  have h : persistenceKernel M hbc (le_refl c) = ⊥ := by
    unfold persistenceKernel
    rw [structureMapLinear_self]
    simp
  unfold persistenceMeasureValue PersistenceMeasureSpace
  rw [h]
  exact Module.finrank_eq_zero_of_subsingleton k _

end TDA.Persistence
