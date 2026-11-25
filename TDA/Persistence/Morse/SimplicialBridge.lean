import TDA.Persistence.Morse.MatchingSchedule
import TDA.Persistence.Reduction.FiniteInputCycleFillingCorrectness
import TDA.Persistence.SublevelInterleaving
import TDA.Persistence.FiniteRankProjectiveResolution

/-!
# The simplicial bridge and the Morse persistence theorem

For a valid finite input `xs`, `boundaryHomologyEquiv h p a` identifies the grade-sublevel
homology of the boundary complex `(degree xs, fun i => (xs.get i).2, FiniteInput.boundary xs)`
with the simplicial homology of `(FiniteInput.gradeFilter xs h).sublevel a` over `ZMod 2`, and
`boundaryHomologyIso h p` assembles these into a natural isomorphism onto
`sublevelModule (ZMod 2) (FiniteInput.gradeFilter xs h) p`. The route stays on `Fin xs.length`:
`boundaryCycleCoordinates` restricts the reducer's `rawCycleCoordinates` to the sublevel cycles
(which are the `CycleInput` vectors); on a valid input its kernel is the sublevel boundaries,
by the executable filling `fillingVector` and `rawCycleCoordinates_eq_zero_iff_boundary`, and it
is surjective onto the coordinates of `sublevelCoordinates`. Classes go to `vectorSublevelClass`
(`boundaryHomologyEquiv_mk`), so naturality is `vectorSublevelClass_naturality`.

For a certified matching `c`, `c.morseSublevelModuleIso h p` composes the inverse bridge with
`c.morseHomologyIso h p`: the simplicial sublevel persistence module is naturally isomorphic to
the persistence module of the Morse complex `c.morseDifferential`, with equal dimensions
(`finrank_simplicialHomology_eq`) and structure-map ranks
(`rankOfStructureMap_sublevelModule_eq`).

This is a library derivation, on sublevel homology only: this module provides no chain-level
isomorphism with `simplicialChainComplex`, no barcode or interval decomposition, no comparison
with the reducer's barcode and no gradient-path formula.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.SimplicialBridge

open CategoryTheory TDA.Simplicial TDA.Persistence.Reduction FiniteInput
open TDA.Persistence.Morse.Cancellation

variable {xs : Input}

/-- On a valid input, support in grades `≤ a` is support in the positions before
`sublevelStage xs a`. -/
theorem sublevelSupported_iff_prefixSupported (h : Valid xs) (a : ℤ)
    (v : Fin xs.length → ZMod 2) :
    SublevelSupported (fun i => (xs.get i).2) a v ↔ PrefixSupported (sublevelStage xs a) v :=
  sublevelSupported_iff_prefixSupported_of_iff (grade_le_iff_index_lt_stage xs h a) v

variable (xs) in
/-- `FiniteInput.CycleInput` is membership in the sublevel cycles of the boundary complex. -/
theorem cycleInput_iff_mem_sublevelCycles (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) :
    CycleInput xs p a v ↔
      v ∈ sublevelCycles (degree xs) (fun i => (xs.get i).2) (boundary xs) p a := by
  rw [mem_sublevelCycles]
  constructor
  · rintro ⟨hs, hz⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_, hz⟩
    · by_contra hn
      exact hi (hs i hn).1
    · by_contra hn
      exact absurd (hs i hn).2 (not_le.mpr hi)
  · rintro ⟨hd, hg, hz⟩
    refine ⟨fun i hi => ⟨?_, ?_⟩, hz⟩
    · by_contra hn
      exact hi (hd i hn)
    · by_contra hn
      exact hi (hg i (lt_of_not_ge hn))

variable (xs) in
/-- The reducer's cycle coordinates of the sublevel cycles of the boundary complex. -/
def boundaryCycleCoordinates (p : ℕ) (a : ℤ) :
    sublevelCycles (degree xs) (fun i => (xs.get i).2) (boundary xs) p a →ₗ[ZMod 2]
      (BasisIndex xs p a → ZMod 2) :=
  rawCycleCoordinates xs p a ∘ₗ Submodule.subtype _

/-- On a valid input, a sublevel cycle has zero coordinates exactly when it is a sublevel
boundary. -/
theorem boundaryCycleCoordinates_eq_zero_iff (h : Valid xs) {p : ℕ} {a : ℤ}
    (z : sublevelCycles (degree xs) (fun i => (xs.get i).2) (boundary xs) p a) :
    boundaryCycleCoordinates xs p a z = 0 ↔
      (z : Fin xs.length → ZMod 2) ∈
        sublevelBoundaries (degree xs) (fun i => (xs.get i).2) (boundary xs) p a := by
  have hv := (cycleInput_iff_mem_sublevelCycles xs p a z).mpr z.2
  constructor
  · intro hz
    obtain ⟨hpre, hdeg⟩ := fillingVector_supported xs h p a z
    exact mem_sublevelBoundaries.mpr ⟨_, hdeg,
      (sublevelSupported_iff_prefixSupported h a _).mpr hpre,
      fillingVector_boundary xs h p a z hv hz⟩
  · intro hb
    obtain ⟨w, hwd, hws, hw⟩ := mem_sublevelBoundaries.mp hb
    have hwpre := (sublevelSupported_iff_prefixSupported h a w).mp hws
    apply (rawCycleCoordinates_eq_zero_iff_boundary xs h p a z hv).mpr
    let := faceFintype xs h
    have hc := (cycleInput_iff_originalCycle xs h p a z).mp hv
    let hi := prefix_le_sublevel xs h a (sublevelStage xs a) le_rfl
    let B := simplicialChain xs h (p + 1) (sublevelStage xs a) w hwpre hwd
    rw [mem_simplicialBoundaries_iff]
    refine ⟨chainIncl (ZMod 2) hi (p + 1) B, ?_⟩
    have he := LinearMap.congr_fun (boundary_chainIncl (ZMod 2) hi p) B
    change TDA.Simplicial.boundary _ _ p (chainIncl (ZMod 2) hi (p + 1) B) =
      chainIncl (ZMod 2) hi p (TDA.Simplicial.boundary _ _ p B) at he
    rw [simplicialChain_boundary xs h p _ z w hc.1 hc.2.1 hwpre hwd hw] at he
    exact he

/-- On a valid input, every coordinate vector is the coordinates of a sublevel cycle. -/
theorem boundaryCycleCoordinates_surjective (h : Valid xs) (p : ℕ) (a : ℤ) :
    Function.Surjective (boundaryCycleCoordinates xs p a) := by
  rw [← LinearMap.range_eq_top, eq_top_iff,
    ← (Pi.basisFun (ZMod 2) (BasisIndex xs p a)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨chainVector (basisRecord xs p a i).cycle,
    (cycleInput_iff_mem_sublevelCycles xs p a _).mp (basisRecord_cycleInput xs h p a i)⟩, ?_⟩
  rw [Pi.basisFun_apply]
  exact rawCycleCoordinates_basisRecord xs p a i

/-- On a valid input, the kernel of `boundaryCycleCoordinates` is the sublevel boundaries among
the sublevel cycles. -/
theorem ker_boundaryCycleCoordinates (h : Valid xs) (p : ℕ) (a : ℤ) :
    LinearMap.ker (boundaryCycleCoordinates xs p a) =
      (sublevelBoundaries (degree xs) (fun i => (xs.get i).2) (boundary xs) p a).comap
        (sublevelCycles (degree xs) (fun i => (xs.get i).2) (boundary xs) p a).subtype := by
  ext z
  rw [LinearMap.mem_ker, Submodule.mem_comap, boundaryCycleCoordinates_eq_zero_iff h]
  rfl

/-- **Per-grade bridge.** On a valid input, the grade-sublevel homology of the boundary
complex is the simplicial homology of the grade-`≤ a` sublevel complex. -/
noncomputable def boundaryHomologyEquiv (h : Valid xs) (p : ℕ) (a : ℤ) :
    sublevelHomology (degree xs) (fun i => (xs.get i).2) (boundary xs) p a ≃ₗ[ZMod 2]
      simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p :=
  ((Submodule.quotEquivOfEq _ _ (ker_boundaryCycleCoordinates h p a).symm).trans
    ((boundaryCycleCoordinates xs p a).quotKerEquivOfSurjective
      (boundaryCycleCoordinates_surjective h p a))).trans (sublevelCoordinates xs h p a).symm

/-- The bridge sends the class of a sublevel cycle to its actual simplicial class. -/
theorem boundaryHomologyEquiv_mk (h : Valid xs) (p : ℕ) (a : ℤ)
    (z : sublevelCycles (degree xs) (fun i => (xs.get i).2) (boundary xs) p a) :
    boundaryHomologyEquiv h p a (Submodule.Quotient.mk z) =
      vectorSublevelClass xs h p a z ((cycleInput_iff_mem_sublevelCycles xs p a z).mpr z.2) := by
  change (sublevelCoordinates xs h p a).symm (rawCycleCoordinates xs p a z) = _
  rw [rawCycleCoordinates_correct xs h p a z, LinearEquiv.symm_apply_apply]

/-- The bridge commutes with the structure maps. -/
theorem boundaryHomologyEquiv_naturality (h : Valid xs) (p : ℕ) {a b : ℤ} (hab : a ≤ b)
    (x : sublevelHomology (degree xs) (fun i => (xs.get i).2) (boundary xs) p a) :
    (simplicialHomologyIncl (ZMod 2) ((gradeFilter xs h).sublevel_mono hab) p).hom
        (boundaryHomologyEquiv h p a x) =
      boundaryHomologyEquiv h p b
        (sublevelHomologyMap (degree xs) (fun i => (xs.get i).2) (boundary xs) p hab x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [sublevelHomologyMap_mk, boundaryHomologyEquiv_mk, boundaryHomologyEquiv_mk]
    exact vectorSublevelClass_naturality xs h p a b hab z _ _

/-- **The simplicial bridge.** On a valid input, in every degree `p`, the grade-sublevel
homology persistence module of the boundary complex is naturally isomorphic to the simplicial
sublevel persistence module of `FiniteInput.gradeFilter`. -/
noncomputable def boundaryHomologyIso (h : Valid xs) (p : ℕ) :
    sublevelHomologyPModule (degree xs) (fun i => (xs.get i).2) (boundary xs) p ≅
      sublevelModule (ZMod 2) (gradeFilter xs h) p :=
  NatIso.ofComponents (fun a => (boundaryHomologyEquiv h p a).toModuleIso) (fun {a b} f => by
    ext x
    exact (boundaryHomologyEquiv_naturality h p (leOfHom f) x).symm)

/-- The components of `boundaryHomologyIso` are `boundaryHomologyEquiv`. -/
@[simp] theorem boundaryHomologyIso_hom_app (h : Valid xs) (p : ℕ) (a : ℤ) :
    ((boundaryHomologyIso h p).hom.app a).hom = (boundaryHomologyEquiv h p a).toLinearMap :=
  rfl

/-- The components of the inverse of `boundaryHomologyIso` are the inverse equivalences. -/
@[simp] theorem boundaryHomologyIso_inv_app (h : Valid xs) (p : ℕ) (a : ℤ) :
    ((boundaryHomologyIso h p).inv.app a).hom = (boundaryHomologyEquiv h p a).symm.toLinearMap :=
  rfl

/-- On a valid input, the grade-sublevel homology of the boundary complex and the simplicial
sublevel homology have equal dimensions. -/
theorem finrank_sublevelHomology_boundary (h : Valid xs) (p : ℕ) (a : ℤ) :
    Module.finrank (ZMod 2)
        (sublevelHomology (degree xs) (fun i => (xs.get i).2) (boundary xs) p a) =
      Module.finrank (ZMod 2) (simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p) :=
  (boundaryHomologyEquiv h p a).finrank_eq

end TDA.Persistence.Morse.SimplicialBridge

namespace TDA.Persistence.Morse.MatchingInput.CertifiedMatching

open CategoryTheory TDA.Simplicial TDA.Persistence.Reduction FiniteInput
open TDA.Persistence.Morse.Cancellation TDA.Persistence.Morse.SimplicialBridge

variable {xs : Input}

/-- **Morse persistence theorem.** On a valid input, for a certified matching `c` and in every
degree `p`, the simplicial sublevel persistence module of `FiniteInput.gradeFilter` is naturally
isomorphic to the grade-sublevel homology persistence module of the Morse complex of `c` on its
critical generators. -/
noncomputable def morseSublevelModuleIso (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ) :
    sublevelModule (ZMod 2) (gradeFilter xs h) p ≅
      sublevelHomologyPModule (degree xs ∘ Subtype.val) ((fun i => (xs.get i).2) ∘ Subtype.val)
        c.morseDifferential p :=
  (boundaryHomologyIso h p).symm ≪≫ c.morseHomologyIso h p

/-- The components of `morseSublevelModuleIso` are the inverse bridge followed by the projection
of the Morse contraction. -/
@[simp] theorem morseSublevelModuleIso_hom_app (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ)
    (a : ℤ) :
    ((c.morseSublevelModuleIso h p).hom.app a).hom =
      (c.morseContraction h).homologyProj p a ∘ₗ (boundaryHomologyEquiv h p a).symm.toLinearMap :=
  rfl

/-- The components of the inverse of `morseSublevelModuleIso` are the inclusion of the Morse
contraction followed by the bridge. -/
@[simp] theorem morseSublevelModuleIso_inv_app (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ)
    (a : ℤ) :
    ((c.morseSublevelModuleIso h p).inv.app a).hom =
      (boundaryHomologyEquiv h p a).toLinearMap ∘ₗ (c.morseContraction h).homologyIncl p a :=
  rfl

/-- The main theorem sends the actual simplicial class of a sublevel cycle vector `v` to the
class of its projection `proj v` in the Morse complex. -/
theorem morseSublevelModuleIso_hom_vectorSublevelClass (c : CertifiedMatching xs) (h : Valid xs)
    (p : ℕ) (a : ℤ) (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    ((c.morseSublevelModuleIso h p).hom.app a).hom (vectorSublevelClass xs h p a v hv) =
      Submodule.Quotient.mk ⟨(c.morseContraction h).proj.mulVec v,
        (c.morseContraction h).proj_mem_sublevelCycles
          ((cycleInput_iff_mem_sublevelCycles xs p a v).mp hv)⟩ := by
  have he := boundaryHomologyEquiv_mk h p a
    ⟨v, (cycleInput_iff_mem_sublevelCycles xs p a v).mp hv⟩
  change (c.morseContraction h).homologyProj p a
    ((boundaryHomologyEquiv h p a).symm (vectorSublevelClass xs h p a v hv)) = _
  rw [← he, LinearEquiv.symm_apply_apply]
  rfl

/-- At every grade, the simplicial sublevel homology of the input and the sublevel homology of
the Morse complex have equal dimensions. -/
theorem finrank_simplicialHomology_eq (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ)
    (a : ℤ) :
    Module.finrank (ZMod 2) (simplicialHomology ((gradeFilter xs h).sublevel a) (ZMod 2) p) =
      Module.finrank (ZMod 2) (sublevelHomology (degree xs ∘ Subtype.val)
        ((fun i => (xs.get i).2) ∘ Subtype.val) c.morseDifferential p a) :=
  ((boundaryHomologyEquiv h p a).symm.trans
    ((c.morseContraction h).sublevelHomologyEquiv p a)).finrank_eq

/-- The structure maps of the simplicial sublevel persistence module and of the Morse persistence
module have equal ranks. -/
theorem rankOfStructureMap_sublevelModule_eq (c : CertifiedMatching xs) (h : Valid xs)
    (p : ℕ) {a b : ℤ} (hab : a ≤ b) :
    rankOfStructureMap (sublevelModule (ZMod 2) (gradeFilter xs h) p) hab =
      rankOfStructureMap (sublevelHomologyPModule (degree xs ∘ Subtype.val)
        ((fun i => (xs.get i).2) ∘ Subtype.val) c.morseDifferential p) hab :=
  rankOfStructureMap_iso hab (c.morseSublevelModuleIso h p)

end TDA.Persistence.Morse.MatchingInput.CertifiedMatching
