import TDA.Mapper.MapperReebPerturbation
import TDA.Reeb.IntervalTranslation

/-!
# Translation of categorical Mapper reconstructions

For `f : C(X, ℝ)`, an interval family `U` and `c : ℝ`, translating the height to `f + c` and
every member to `U i + c = translate (-c) (U i)` translates the assembled precosheaf:
`coverComponentsTranslateIso` identifies `coverComponents (f + c) (U + c)` with
`translatePre c (coverComponents f U)`. Hence the two are at interleaving distance at most `|c|`.

For a finite bounded-interval cover `U i = (a i, b i)` with at least one active member, that is
a member with nonempty inverse image, the distance is exactly `|c|`
(`interleavingDistance_coverComponents_add_const`). For `c > 0` and `ε < c`, take an active
member with least left endpoint `a i₀` and a short interval `I` starting at `a i₀`: the
assembled value of `f` at `I` is nonempty, while every member that meets the translated
thickening of `I` lies below `a i₀` and is therefore inactive. No coverage or boundedness of `f`
is needed.

For vertex heights `h` on a finite graph `G`, write `M_h(a, b)` for
`graphPLMapperReconstruction G h a b`. With an active member,
`d_geo(M_h(a, b), M_(h + c)(a + c, b + c)) = |c|` at every finite cover
(`geometricInterleavingDistance_graphPLMapperReconstruction_add_const`); coverage of the
attained range on a nonempty vertex type supplies the active member. Without an active member
the conclusion fails: the empty cover reconstructs the empty graph, and two empty graphs are at
distance `0` (`geometricInterleavingDistance_graphPLMapperReconstruction_of_isEmpty`).

These are library statements; no translation functor on graph objects is constructed, and the
exact values are proved through the cosheaf identification of the reconstructions.
See `docs/math/mapper-reeb-approximation.md`.
-/

open Set CategoryTheory
open scoped NNReal ENNReal

universe u v

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval TDA.Reeb.GraphPL

section Cover

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- A height `y + c` lies in the saturation of `I` by the translated family exactly when `y`
lies in the saturation of `I - c` by the original family. -/
theorem add_const_mem_coverSaturation_translate_iff (U : ι → OpenInterval) (c : ℝ)
    (I : OpenInterval) {y : ℝ} :
    y + c ∈ coverSaturation (fun i => translate (-c) (U i)) I ↔
      y ∈ coverSaturation U (translate c I) := by
  simp only [mem_coverSaturation, mem_translate]
  constructor
  · rintro ⟨i, hy, z, hz, hzI⟩
    exact ⟨i, by simpa using hy, z - c, hz, by simpa using hzI⟩
  · rintro ⟨i, hy, z, hz, hzI⟩
    exact ⟨i, by simpa using hy, z + c, by simpa using hz, hzI⟩

/-- The inverse image of the translated saturation under `f + c` is the inverse image of the
original saturation of `I - c` under `f`. -/
theorem preimage_coverSaturation_add_const (f : C(X, ℝ)) (U : ι → OpenInterval) (c : ℝ)
    (I : OpenInterval) :
    (f + ContinuousMap.const X c) ⁻¹' (coverSaturation (fun i => translate (-c) (U i)) I) =
      f ⁻¹' (coverSaturation U (translate c I)) :=
  Set.ext fun x => add_const_mem_coverSaturation_translate_iff U c I (y := f x)

/-- Two interval-indexed families of open sets with equal inverse images, under `g` and `f`
respectively, have naturally isomorphic inverse-image components. -/
private def preimageComponentsIso {f g : C(X, ℝ)} (P Q : OpenInterval ⥤ TopologicalSpace.Opens ℝ)
    (hPQ : ∀ I, g ⁻¹' (P.obj I : Set ℝ) = f ⁻¹' (Q.obj I : Set ℝ)) :
    P ⋙ componentFunctor g ≅ Q ⋙ componentFunctor f :=
  NatIso.ofComponents (fun I =>
    { hom := TypeCat.ofHom (componentMap (ContinuousMap.inclusion (hPQ I).le))
      inv := TypeCat.ofHom (componentMap (ContinuousMap.inclusion (hPQ I).ge))
      hom_inv_id := by
        ext p
        induction p using ZerothHomotopy.rec with
        | mk x => rfl
      inv_hom_id := by
        ext p
        induction p using ZerothHomotopy.rec with
        | mk x => rfl }) fun _ => by
    ext p
    induction p using ZerothHomotopy.rec with
    | mk x => rfl

/-- Translating the height and every cover member by `c` translates the assembled precosheaf by
`c`. The component at `I` sends the class of a point to the class of the same point. -/
def coverComponentsTranslateIso (f : C(X, ℝ)) (U : ι → OpenInterval) (c : ℝ) :
    coverComponents (f + ContinuousMap.const X c) (fun i => translate (-c) (U i)) ≅
      translatePre c (coverComponents f U) :=
  preimageComponentsIso (coverSaturationFunctor fun i => translate (-c) (U i))
    (translateFunctor c ⋙ coverSaturationFunctor U)
    (preimage_coverSaturation_add_const f U c) ≪≫ Functor.associator _ _ _

/-- The translated assembly is within `‖c‖₊` of the original one. -/
theorem interleavingDistance_coverComponents_translate_le (f : C(X, ℝ)) (U : ι → OpenInterval)
    (c : ℝ) :
    interleavingDistance (coverComponents f U)
      (coverComponents (f + ContinuousMap.const X c) (fun i => translate (-c) (U i))) ≤ ‖c‖₊ := by
  rw [interleavingDistance_congr (Iso.refl _) (coverComponentsTranslateIso f U c)]
  exact interleavingDistance_translatePre_le c _

variable [Finite ι]

/-- Lower bound for a positive translation of a bounded-interval cover with an active member. -/
private theorem coe_le_interleavingDistance_coverComponents_add_const (f : C(X, ℝ))
    (a b : ι → ℝ) (hact : ∃ i, (f ⁻¹' (ioo (a i) (b i) : Set ℝ)).Nonempty) {c : ℝ}
    (hc : 0 < c) :
    ((‖c‖₊ : ℝ≥0) : ℝ≥0∞) ≤ interleavingDistance (coverComponents f fun i => ioo (a i) (b i))
      (coverComponents (f + ContinuousMap.const X c) fun i => ioo (a i + c) (b i + c)) := by
  classical
  have := Fintype.ofFinite ι
  let S := Finset.univ.filter fun i => (f ⁻¹' (ioo (a i) (b i) : Set ℝ)).Nonempty
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hact
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image a hS
  obtain ⟨x₀, hx₀⟩ := (Finset.mem_filter.1 hi₀).2
  have hx₀' : a i₀ < f x₀ ∧ f x₀ < b i₀ := hx₀
  refine le_interleavingDistance_of_forall_exists_isEmpty fun ε hε => ?_
  have hεc : (ε : ℝ) < c := by
    have := ENNReal.coe_lt_coe.1 hε
    rwa [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_of_nonneg hc.le] at this
  set η := (c - ε) / 2 with hη_def
  have hη : 0 < η := by linarith
  set m := min (b i₀ - a i₀) η with hm_def
  have hm : 0 < m := lt_min (by linarith) hη
  have hm₁ : m ≤ b i₀ - a i₀ := min_le_left _ _
  have hm₂ : m ≤ η := min_le_right _ _
  have hy₀ : a i₀ < a i₀ + m / 2 := by linarith
  have hy₁ : a i₀ + m / 2 < b i₀ := by linarith
  have hy₂ : a i₀ + m / 2 < a i₀ + η := by linarith
  refine ⟨ioo (a i₀) (a i₀ + η), ⟨ZerothHomotopy.mk ⟨x₀, mem_coverSaturation.2
    ⟨i₀, hx₀, a i₀ + m / 2, ⟨hy₀, hy₁⟩, ⟨hy₀, hy₂⟩⟩⟩⟩, ⟨fun p => ?_⟩⟩
  induction p using ZerothHomotopy.rec with
  | mk x =>
    obtain ⟨i, hxi, z, hz, hzI⟩ := mem_coverSaturation.1 x.2
    have hxi' : a i + c < f x + c ∧ f x + c < b i + c := hxi
    have hz' : a i + c < z := hz.1
    obtain ⟨w, hw, hzw⟩ := mem_thicken.1 hzI
    have hw' : w < a i₀ + η := hw.2
    have hi : i ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_univ i, x.1, show a i < f x.1 ∧ f x.1 < b i by constructor <;> linarith⟩
    have := hmin i hi
    linarith [(abs_le.1 hzw).2]

/-- For a finite bounded-interval cover with an active member, translating the height and the
cover by `c` moves the assembled precosheaf by exactly `‖c‖₊`. -/
theorem interleavingDistance_coverComponents_add_const (f : C(X, ℝ)) (a b : ι → ℝ) (c : ℝ)
    (hact : ∃ i, (f ⁻¹' (ioo (a i) (b i) : Set ℝ)).Nonempty) :
    interleavingDistance (coverComponents f fun i => ioo (a i) (b i))
      (coverComponents (f + ContinuousMap.const X c) fun i => ioo (a i + c) (b i + c)) =
      ‖c‖₊ := by
  refine le_antisymm ?_ ?_
  · have hU : (fun i => ioo (a i + c) (b i + c)) = fun i => translate (-c) (ioo (a i) (b i)) := by
      funext i
      rw [translate_ioo, sub_neg_eq_add, sub_neg_eq_add]
    rw [hU]
    exact interleavingDistance_coverComponents_translate_le f _ c
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hact' : ∃ i, ((f + ContinuousMap.const X c) ⁻¹'
        (ioo (a i + c) (b i + c) : Set ℝ)).Nonempty := by
      obtain ⟨i, x, hx⟩ := hact
      have hx' : a i < f x ∧ f x < b i := hx
      exact ⟨i, x, show a i + c < f x + c ∧ f x + c < b i + c by constructor <;> linarith⟩
    have := coe_le_interleavingDistance_coverComponents_add_const (f + ContinuousMap.const X c)
      (fun i => a i + c) (fun i => b i + c) hact' (neg_pos.2 hc)
    have hback : f + ContinuousMap.const X c + ContinuousMap.const X (-c) = f := by ext; simp
    simp only [add_neg_cancel_right, hback, nnnorm_neg] at this
    rwa [interleavingDistance_comm]
  · simp
  · exact coe_le_interleavingDistance_coverComponents_add_const f a b hact hc

end Cover

noncomputable section

section Graph

variable {ι ι' : Type} [Finite ι] [Finite ι'] {V : Type} [Finite V] (G : SimpleGraph V)
  (h : V → ℝ)

/-- For vertex heights on a finite graph and a finite cover with an active member, the
reconstructions of `h` over `(a, b)` and of `h + c` over `(a + c, b + c)` are at geometric
interleaving distance exactly `|c|`. -/
theorem geometricInterleavingDistance_graphPLMapperReconstruction_add_const (a b : ι → ℝ)
    (c : ℝ) (hact : ∃ i, (plHeight G h ⁻¹' (ioo (a i) (b i) : Set ℝ)).Nonempty) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G (fun v => h v + c) (fun i => a i + c)
        (fun i => b i + c)) = ENNReal.ofReal |c| := by
  rw [geometricInterleavingDistance_graphPLMapperReconstruction_eq, plHeight_add_const,
    interleavingDistance_coverComponents_add_const _ a b c hact, ← Real.enorm_eq_ofReal_abs]
  rfl

/-- On a nonempty vertex type, a cover of the attained range has an active member, so the
translated reconstruction is at geometric interleaving distance exactly `|c|`. -/
theorem geometricInterleavingDistance_graphPLMapperReconstruction_add_const_of_covers
    [Nonempty V] (a b : ι → ℝ) (c : ℝ) (hcov : ∀ x, ∃ i, plHeight G h x ∈ ioo (a i) (b i)) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G (fun v => h v + c) (fun i => a i + c)
        (fun i => b i + c)) = ENNReal.ofReal |c| := by
  obtain ⟨i, hi⟩ := hcov (GraphRealization.vertex G (Classical.arbitrary V))
  exact geometricInterleavingDistance_graphPLMapperReconstruction_add_const G h a b c
    ⟨i, _, hi⟩

/-- The empty cover reconstructs the empty graph. -/
theorem isEmpty_graphPLMapperReconstruction_of_isEmpty_cover [IsEmpty ι] (a b : ι → ℝ) :
    IsEmpty (graphPLMapperReconstruction G h a b).obj.left := by
  refine ⟨fun x => ?_⟩
  let t := overBaseMap (graphPLMapperReconstruction G h a b).obj x
  let I : OpenInterval := ioo (t - 1) (t + 1)
  have hx : t ∈ I := ⟨by simp, by simp⟩
  have p : ((RGraph.cosheafFunctor.obj (graphPLMapperReconstruction G h a b)).obj).obj I :=
    ZerothHomotopy.mk ⟨x, hx⟩
  have q := (categoricalMapperReconstructionIso (plHeight G h) a b
    (fun i => finite_zerothHomotopy G h (ioo (a i) (b i)))).hom.app I p
  induction q using ZerothHomotopy.rec with
  | mk y =>
    obtain ⟨i, -⟩ := mem_coverSaturation.mp y.2
    exact isEmptyElim i

/-- Reconstructions over empty covers are at geometric interleaving distance `0`, for any two
vertex heights. -/
theorem geometricInterleavingDistance_graphPLMapperReconstruction_of_isEmpty [IsEmpty ι]
    [IsEmpty ι'] (g : V → ℝ) (a b : ι → ℝ) (a' b' : ι' → ℝ) :
    RGraph.geometricInterleavingDistance (graphPLMapperReconstruction G h a b)
      (graphPLMapperReconstruction G g a' b') = 0 :=
  RGraph.geometricInterleavingDistance_eq_zero_of_isEmpty
    (isEmpty_graphPLMapperReconstruction_of_isEmpty_cover G h a b)
    (isEmpty_graphPLMapperReconstruction_of_isEmpty_cover G g a' b')

end Graph

end

end TDA.Mapper
