import TDA.Reeb.ConstructibleCosheaf
import TDA.Reeb.ComponentsExamples
import Mathlib.Analysis.Convex.PathConnected

/-!
# Constructible cosheaf fixtures

Fixtures for `TDA.Reeb.CriticalValues.natTransEquivShortMaps` and its supporting geometry. Every
cosheaf below is an actual interval component functor with the merged cosheaf law
`intervalComponents_isIntervalCosheaf`; no table of values stands in for a cosheaf.

* Singleton levels `S1 = {0}`: the only star is `ℝ`, there are no gaps, the tails are the two
  rays, and an interval containing `0` has envelope `ℝ`.
* The zero cosheaf (components of the empty space), constructible at every list of levels, and
  the point cosheaf (components of one point at height `0`), constructible at `S1`; every
  endomorphism of the point cosheaf is an isomorphism by the short-interval criterion.
* Three levels `S3 = {0, 1, 2}`: stars, gaps, their cover of `ℝ` and overlaps; envelopes of rays,
  of `ℝ` and of a ray in the lower tail; two disjoint subintervals of one gap with the same
  envelope although their intersection has envelope `⊥`; gluing over the three stars, over the
  two stars of `(-∞, 2)`, over a strict refinement, and the fringe gap `(1, 2)` of `(-∞, 2)`.
* The strip `A × [0, 2] → ℝ` for a finite discrete `A`, at `S2 = {0, 2}`: its components are
  classified by the first coordinate, and it satisfies the corrected predicate
  (`strip_isConstructibleAt`). For `A` a point it refutes the rule without the nonemptiness of
  the source (`uncorrected_rule_fails`, paired in `strip_corrected_not_uncorrected`). Its
  extracted data at `S2` are singletons with bijective endpoint maps.
* The collapse `Bool × [0, 2] → PUnit × [0, 2]` merges the two regular components over `(0, 2)`,
  so it is not an isomorphism by the short-interval criterion.
* Refinement `{0, 2} → {0, 1, 2}`: the strip stays constructible and the envelope shrinks.
* Levels `{0, 2, 3}`: the two gaps meet no level, yet the strip has a nonempty value on one and an
  empty value on the other, so equal (empty) critical hits do not identify gap values.
* Finite data: zero data, isolated vertices, parallel edges with a noninjective endpoint, a
  noninjective collapse map, and an automorphism inverted through `FiniteReebData.Hom.inv`.
-/

open Set CategoryTheory TDA.Topology

universe u w

namespace TDA.Reeb.Examples.Constructible

noncomputable section

open TDA.Reeb TDA.Reeb.OpenInterval

/-- Two maps between subsingleton types are bijective once nonemptiness of the target gives
nonemptiness of the source. -/
theorem bijective_of_subsingleton {α β : Sort*} [Subsingleton α] [Subsingleton β] (f : α → β)
    (h : Nonempty β → Nonempty α) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun b =>
    let ⟨a⟩ := h ⟨b⟩; ⟨a, Subsingleton.elim _ _⟩⟩

/-! ### Singleton levels, the zero cosheaf and the point cosheaf -/

/-- The singleton list of levels `{0}`. -/
def S1 : CriticalValues 0 :=
  ⟨![0], fun i j h => by have := i.isLt; have := j.isLt; rw [Fin.lt_def] at h; exfalso; omega⟩

theorem S1_value (i : Fin 1) : S1.value i = 0 := by
  rw [Subsingleton.elim i 0]; rfl

/-- The only star of `S1` is `ℝ`. -/
theorem S1_J (i : Fin 1) : S1.J i = ⊤ := by
  rw [Subsingleton.elim i 0]; exact S1.J_eq_top_of_zero

theorem S1_lowerTail : S1.lowerTail = iio 0 := by simp [CriticalValues.lowerTail, S1]
theorem S1_upperTail : S1.upperTail = ioi 0 := by simp [CriticalValues.upperTail, S1]

/-- An interval containing `0` has envelope `ℝ` at `S1`. -/
theorem S1_envelope_of_mem {I : OpenInterval} (h : (0 : ℝ) ∈ I) : S1.envelope I = ⊤ :=
  le_antisymm le_top ((S1_J 0).symm.le.trans (S1.J_le_envelope (by rwa [S1_value])))

/-- The zero cosheaf: interval components of the empty space. -/
def zeroCosheaf : OpenInterval ⥤ Type := intervalComponents (ContinuousMap.const PEmpty.{1} (0 : ℝ))

theorem zeroCosheaf_isIntervalCosheaf : IsIntervalCosheaf.{w} zeroCosheaf :=
  intervalComponents_isIntervalCosheaf _

theorem zeroCosheaf_isEmpty (I : OpenInterval) : IsEmpty (zeroCosheaf.obj I) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact x.1.elim⟩

/-- The zero cosheaf is constructible at every list of levels. -/
theorem zeroCosheaf_isConstructibleAt {n : ℕ} (S : CriticalValues n) :
    S.IsConstructibleAt zeroCosheaf where
  finite I := by have := zeroCosheaf_isEmpty I; infer_instance
  bijective I _ _ _ _ := by
    have := zeroCosheaf_isEmpty I
    exact ⟨fun a => isEmptyElim a, fun b => isEmptyElim ((zeroCosheaf_isEmpty _).false b)⟩
  isEmpty_lowerTail := zeroCosheaf_isEmpty _
  isEmpty_upperTail := zeroCosheaf_isEmpty _

/-- The extracted data of the zero cosheaf have empty vertex and edge types. -/
theorem zeroCosheaf_extract_isEmpty {n : ℕ} (S : CriticalValues n) :
    (∀ i, IsEmpty ((S.extract zeroCosheaf (zeroCosheaf_isConstructibleAt S).finite).V i)) ∧
      ∀ e, IsEmpty ((S.extract zeroCosheaf (zeroCosheaf_isConstructibleAt S).finite).E e) :=
  ⟨fun _ => zeroCosheaf_isEmpty _, fun _ => zeroCosheaf_isEmpty _⟩

/-- The point cosheaf: interval components of one point at height `0`. -/
def pointCosheaf : OpenInterval ⥤ Type :=
  intervalComponents (ContinuousMap.const PUnit.{1} (0 : ℝ))

theorem pointCosheaf_isIntervalCosheaf : IsIntervalCosheaf.{w} pointCosheaf :=
  intervalComponents_isIntervalCosheaf _

instance pointCosheaf_subsingleton (I : OpenInterval) : Subsingleton (pointCosheaf.obj I) :=
  ⟨fun a b => by
    induction a using ZerothHomotopy.rec with
    | mk x =>
      induction b using ZerothHomotopy.rec with
      | mk y => rw [Subsingleton.elim x y]⟩

theorem pointCosheaf_nonempty_iff (I : OpenInterval) :
    Nonempty (pointCosheaf.obj I) ↔ (0 : ℝ) ∈ I :=
  ⟨fun ⟨c⟩ => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact x.2,
   fun h => ⟨ZerothHomotopy.mk ⟨PUnit.unit, h⟩⟩⟩

/-- The point cosheaf is constructible at `S1`. -/
theorem pointCosheaf_isConstructibleAt : S1.IsConstructibleAt pointCosheaf where
  finite _ := inferInstance
  bijective I J h _ hhit := bijective_of_subsingleton _ fun hJ => by
    have h0 := (hhit 0).2 (by rw [S1_value]; exact (pointCosheaf_nonempty_iff J).1 hJ)
    rw [S1_value] at h0
    exact (pointCosheaf_nonempty_iff I).2 h0
  isEmpty_lowerTail := not_nonempty_iff.1 fun h => by
    have := (pointCosheaf_nonempty_iff _).1 h
    rw [S1_lowerTail] at this
    exact lt_irrefl _ (mem_iio.1 this)
  isEmpty_upperTail := not_nonempty_iff.1 fun h => by
    have := (pointCosheaf_nonempty_iff _).1 h
    rw [S1_upperTail] at this
    exact lt_irrefl _ (mem_ioi.1 this)

/-- Every endomorphism of the point cosheaf is an isomorphism, by the short-interval criterion
(one star with one-point values, no gaps). -/
theorem pointCosheaf_isIso (α : pointCosheaf ⟶ pointCosheaf) : IsIso α :=
  (S1.isIso_iff_shortIntervals pointCosheaf_isConstructibleAt pointCosheaf_isIntervalCosheaf
    pointCosheaf_isConstructibleAt pointCosheaf_isIntervalCosheaf α).2
    ⟨fun i => bijective_of_subsingleton _ fun _ =>
      (pointCosheaf_nonempty_iff _).2 (by rw [S1_J]; trivial), fun e => e.elim0⟩

/-! ### Three levels `0 < 1 < 2` -/

section threeLevel

/-- Critical values `0 < 1 < 2`. -/
def S3 : CriticalValues 2 :=
  ⟨![0, 1, 2], Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i <;> simp⟩

theorem S3_J0 : S3.J 0 = iio 1 := by
  have h₂ : S3.upperCut 0 = ((1 : ℝ) : EReal) := by
    rw [show (0 : Fin 3) = Fin.castSucc (0 : Fin 2) from rfl, S3.upperCut_castSucc]; simp [S3]
  ext x
  rw [S3.mem_J, CriticalValues.lowerCut_zero, h₂, mem_iio, EReal.coe_lt_coe_iff]
  exact ⟨fun h => h.2, fun h => ⟨EReal.bot_lt_coe x, h⟩⟩

theorem S3_J1 : S3.J 1 = ioo 0 2 := by
  have h₁ : S3.lowerCut 1 = ((0 : ℝ) : EReal) := by
    rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, S3.lowerCut_succ]; simp [S3]
  have h₂ : S3.upperCut 1 = ((2 : ℝ) : EReal) := by
    rw [show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from rfl, S3.upperCut_castSucc]; simp [S3]
  ext x
  rw [S3.mem_J, h₁, h₂, mem_ioo]
  simp

theorem S3_J2 : S3.J 2 = ioi 1 := by
  have h₁ : S3.lowerCut 2 = ((1 : ℝ) : EReal) := by
    rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, S3.lowerCut_succ]; simp [S3]
  have h₂ : S3.upperCut 2 = ⊤ := S3.upperCut_last
  ext x
  rw [S3.mem_J, h₁, h₂, mem_ioi, EReal.coe_lt_coe_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, EReal.coe_lt_top x⟩⟩

theorem S3_K0 : S3.K 0 = ioo 0 1 := by simp [CriticalValues.K, S3]
theorem S3_K1 : S3.K 1 = ioo 1 2 := by simp [CriticalValues.K, S3]
theorem S3_lowerTail : S3.lowerTail = iio 0 := by simp [CriticalValues.lowerTail, S3]

/-- The three stars cover `ℝ`. -/
theorem S3_cover : ⋃ i, (S3.J i : Set ℝ) = (⊤ : OpenInterval) := by
  ext x
  simp only [mem_iUnion, coe_top, mem_univ, iff_true, SetLike.mem_coe]
  rcases lt_or_ge x 1 with h | h
  · exact ⟨0, by rw [S3_J0]; exact h⟩
  rcases lt_or_ge x 2 with h' | h'
  · exact ⟨1, by rw [S3_J1]; exact ⟨by linarith, h'⟩⟩
  · exact ⟨2, by rw [S3_J2]; exact (show (1 : ℝ) < x by linarith)⟩

theorem S3_inf01 : S3.J 0 ⊓ S3.J 1 = S3.K 0 := S3.J_castSucc_inf_J_succ 0
theorem S3_inf12 : S3.J 1 ⊓ S3.J 2 = S3.K 1 := S3.J_castSucc_inf_J_succ 1

/-- Nonadjacent stars do not meet. -/
theorem S3_inf02 : S3.J 0 ⊓ S3.J 2 = ⊥ := S3.J_inf_J_eq_bot (by simp)

/-! Envelopes of rays and of `ℝ`, and non-preservation of intersections. -/

/-- The ray `(-∞, 1/2)` has envelope the first star `(-∞, 1)`. -/
theorem S3_envelope_iio : S3.envelope (iio (1 / 2)) = iio 1 := by
  rw [← S3_J0]
  refine S3.envelope_eq_J (by rw [S3_J0]; exact fun x (hx : x < 1 / 2) => mem_iio.2 (by linarith))
    (mem_iio.2 (by simp [S3]))

/-- The ray `(3/2, ∞)` has envelope the last star `(1, ∞)`. -/
theorem S3_envelope_ioi : S3.envelope (ioi (3 / 2)) = ioi 1 := by
  rw [← S3_J2]
  refine S3.envelope_eq_J (by rw [S3_J2]; exact fun x (hx : 3 / 2 < x) => mem_ioi.2 (by linarith))
    (mem_ioi.2 (by simp [S3]; norm_num))

/-- `ℝ` is its own envelope. -/
theorem S3_envelope_top : S3.envelope ⊤ = ⊤ := le_antisymm le_top (S3.le_envelope ⊤)

/-- A ray inside the lower tail has the lower tail as envelope. -/
theorem S3_envelope_lowerRay : S3.envelope (iio (-1)) = iio 0 := by
  rw [← S3_lowerTail]
  exact S3.envelope_eq_lowerTail (by
    rw [S3_lowerTail]; exact fun x (hx : x < -1) => mem_iio.2 (by linarith))
    ⟨-2, mem_iio.2 (by norm_num)⟩

/-- Two disjoint subintervals of the gap `(0, 1)` both have envelope `(0, 1)`, while their
intersection has envelope `⊥`. -/
theorem S3_envelope_not_inf :
    S3.envelope (ioo (1 / 4) (1 / 3)) = S3.K 0 ∧ S3.envelope (ioo (1 / 2) (3 / 4)) = S3.K 0 ∧
      S3.envelope (ioo (1 / 4) (1 / 3) ⊓ ioo (1 / 2) (3 / 4)) = ⊥ := by
  refine ⟨S3.envelope_eq_K ?_ ⟨0.3, ?_⟩, S3.envelope_eq_K ?_ ⟨0.6, ?_⟩, ?_⟩
  · rw [S3_K0]; exact fun x hx => mem_ioo.2 ⟨by linarith [(mem_ioo.1 hx).1],
      by linarith [(mem_ioo.1 hx).2]⟩
  · exact mem_ioo.2 ⟨by norm_num, by norm_num⟩
  · rw [S3_K0]; exact fun x hx => mem_ioo.2 ⟨by linarith [(mem_ioo.1 hx).1],
      by linarith [(mem_ioo.1 hx).2]⟩
  · exact mem_ioo.2 ⟨by norm_num, by norm_num⟩
  · refine S3.envelope_eq_bot fun ⟨x, hx₁, hx₂⟩ => ?_
    linarith [(mem_ioo.1 hx₁).2, (mem_ioo.1 hx₂).1]

/-- Selected-star cover: the envelope of `(1/2, 3/2)` is the star `(0, 2)` of its only level. -/
theorem S3_envelope_middle : S3.envelope (ioo (1 / 2) (3 / 2)) = ioo 0 2 := by
  rw [← S3_J1]
  exact S3.envelope_eq_J (by
    rw [S3_J1]; exact fun x hx => mem_ioo.2 ⟨by linarith [(mem_ioo.1 hx).1],
      by linarith [(mem_ioo.1 hx).2]⟩) (mem_ioo.2 ⟨by simp [S3]; norm_num, by simp [S3]; norm_num⟩)

variable {F G : OpenInterval ⥤ Type u} (hF : IsIntervalCosheaf.{0} F)

/-- The star family into `G ⊤`: `G(J i ≤ ⊤) ∘ star i`. -/
def starFamily (φ : S3.ShortMaps F G) (i : Fin 3) : F.obj (S3.J i) → G.obj ⊤ :=
  fun x => G.map (homOfLE le_top) (φ.star i x)

/-- Pairwise local compatibility on all nine pairs: diagonal by thinness, adjacent through the
incidence equations, nonadjacent through the empty value at `⊥`. -/
theorem starFamily_compat (hbot : IsEmpty (F.obj ⊥)) (φ : S3.ShortMaps F G) (k l : Fin 3)
    (c : F.obj (S3.J k ⊓ S3.J l)) :
    starFamily φ k (F.map (homOfLE inf_le_left) c) =
      starFamily φ l (F.map (homOfLE inf_le_right) c) := by
  unfold starFamily
  fin_cases k <;> fin_cases l
  · exact congrArg _ (congrArg _ (map_apply_eq_of_thin F _ _ c))
  · exact compat_of_inf_le le_top le_top (S3.K_le_J_castSucc 0) (S3.K_le_J_succ 0)
      S3_inf01.le _ _ (φ.gap 0) (φ.left_comm 0) (φ.right_comm 0) c
  · exact ((isEmpty_of_le_bot hbot S3_inf02.le).false c).elim
  · exact compat_of_inf_le le_top le_top (S3.K_le_J_succ 0) (S3.K_le_J_castSucc 0)
      (by rw [inf_comm]; exact S3_inf01.le) _ _ (φ.gap 0) (φ.right_comm 0) (φ.left_comm 0) c
  · exact congrArg _ (congrArg _ (map_apply_eq_of_thin F _ _ c))
  · exact compat_of_inf_le le_top le_top (S3.K_le_J_castSucc 1) (S3.K_le_J_succ 1)
      S3_inf12.le _ _ (φ.gap 1) (φ.left_comm 1) (φ.right_comm 1) c
  · exact ((isEmpty_of_le_bot hbot (by rw [inf_comm]; exact S3_inf02.le)).false c).elim
  · exact compat_of_inf_le le_top le_top (S3.K_le_J_succ 1) (S3.K_le_J_castSucc 1)
      (by rw [inf_comm]; exact S3_inf12.le) _ _ (φ.gap 1) (φ.right_comm 1) (φ.left_comm 1) c
  · exact congrArg _ (congrArg _ (map_apply_eq_of_thin F _ _ c))

/-- The glued map `F ⊤ → G ⊤` from commuting short maps. -/
def glueTop (φ : S3.ShortMaps F G) : F.obj ⊤ → G.obj ⊤ :=
  hF.glue S3.J S3_cover (starFamily φ) (starFamily_compat hF.isEmpty_obj_bot φ)

theorem glueTop_map (φ : S3.ShortMaps F G) (i : Fin 3) (x : F.obj (S3.J i)) :
    glueTop hF φ (F.map (homOfLE le_top) x) = G.map (homOfLE le_top) (φ.star i x) :=
  hF.glue_map i _ x

theorem eq_glueTop (φ : S3.ShortMaps F G) (g : F.obj ⊤ → G.obj ⊤)
    (hg : ∀ i x, g (F.map (homOfLE le_top) x) = G.map (homOfLE le_top) (φ.star i x)) :
    g = glueTop hF φ :=
  hF.eq_glue g fun i x => (congrArg g (map_apply_eq_of_thin F _ _ x)).trans (hg i x)

/-- One-star cover of `J 1`. -/
theorem J1_cover : ⋃ _ : Unit, (S3.J 1 : Set ℝ) = S3.J 1 := iUnion_const _

/-- The one-star glued map at `J 1`. -/
def glueJ1 (φ : S3.ShortMaps F G) : F.obj (S3.J 1) → G.obj (S3.J 1) :=
  hF.glue (fun _ : Unit => S3.J 1) J1_cover (fun _ => φ.star 1)
    (fun _ _ c => congrArg _ (map_apply_eq_of_thin F _ _ c))

theorem glueJ1_eq (φ : S3.ShortMaps F G) : glueJ1 hF φ = φ.star 1 :=
  (hF.eq_glue (φ.star 1) fun _ x => congrArg _ (map_self_apply _ x)).symm

/-- Fringe-gap naturality square `K 0 ≤ J 1` from the right incidence equation. `K 0` is not an
overlap of two stars selected for `J 1`. -/
theorem fringe_square (φ : S3.ShortMaps F G) (x : F.obj (S3.K 0)) :
    G.map (homOfLE (S3.K_le_J_succ 0)) (φ.gap 0 x) =
      glueJ1 hF φ (F.map (homOfLE (S3.K_le_J_succ 0)) x) := by
  rw [glueJ1_eq]; exact φ.right_comm 0 x

/-- Cover comparison: one-star cover of `J 1` into the three-star cover of `⊤`. -/
theorem glueJ1_comp_map (φ : S3.ShortMaps F G) (x : F.obj (S3.J 1)) :
    G.map (homOfLE le_top) (glueJ1 hF φ x) = glueTop hF φ (F.map (homOfLE le_top) x) :=
  hF.glue_comp_map (le_top : S3.J 1 ≤ ⊤) (fun _ => (1 : Fin 3)) (fun _ => le_rfl)
    (G.map (homOfLE le_top)) (fun _ e => by
      show G.map (homOfLE le_top) (φ.star 1 e) = G.map (homOfLE le_top) (φ.star 1 _)
      rw [map_self_apply]) x

/-- The two stars selected for `U = (-∞, 2)`. -/
def U2 (k : Fin 2) : OpenInterval := S3.J k.castSucc

theorem U2_cover : ⋃ k, (U2 k : Set ℝ) = iio 2 := by
  ext x
  rw [mem_iUnion, Fin.exists_fin_two]
  show x ∈ S3.J 0 ∨ x ∈ S3.J 1 ↔ x ∈ iio 2
  rw [S3_J0, S3_J1, mem_iio, mem_ioo, mem_iio]
  constructor
  · rintro (h | ⟨-, h⟩) <;> linarith
  · intro h
    by_cases h₁ : x < 1
    · exact Or.inl h₁
    · exact Or.inr ⟨by linarith, h⟩

theorem U2_le (k : Fin 2) : U2 k ≤ iio 2 := le_of_iUnion_eq U2_cover k

/-- `(-∞, 2)` is its own envelope; it contains the gap `(1, 2)` at its fringe. -/
theorem S3_envelope_U : S3.envelope (iio 2) = iio 2 := by
  refine le_antisymm (fun x hx => ?_) (S3.le_envelope _)
  obtain ⟨-, h₂⟩ := S3.mem_envelope.1 hx
  exact mem_iio.2 (by simpa [S3] using h₂ 2 fun y (hy : y < 2) => by simpa [S3] using hy)

/-- The two-star family into `G U`. -/
def U2Family (φ : S3.ShortMaps F G) (k : Fin 2) : F.obj (U2 k) → G.obj (iio 2) :=
  fun x => G.map (homOfLE (U2_le k)) (φ.star k.castSucc x)

theorem U2Family_compat (φ : S3.ShortMaps F G) (k l : Fin 2) (c : F.obj (U2 k ⊓ U2 l)) :
    U2Family φ k (F.map (homOfLE inf_le_left) c) =
      U2Family φ l (F.map (homOfLE inf_le_right) c) := by
  unfold U2Family
  fin_cases k <;> fin_cases l
  · exact congrArg _ (congrArg _ (map_apply_eq_of_thin F _ _ c))
  · exact compat_of_inf_le (U2_le 0) (U2_le 1) (S3.K_le_J_castSucc 0) (S3.K_le_J_succ 0)
      S3_inf01.le _ _ (φ.gap 0) (φ.left_comm 0) (φ.right_comm 0) c
  · exact compat_of_inf_le (U2_le 1) (U2_le 0) (S3.K_le_J_succ 0) (S3.K_le_J_castSucc 0)
      (by rw [inf_comm]; exact S3_inf01.le) _ _ (φ.gap 0) (φ.right_comm 0) (φ.left_comm 0) c
  · exact congrArg _ (congrArg _ (map_apply_eq_of_thin F _ _ c))

/-- The glued map at `U = (-∞, 2)` over its two selected stars. -/
def glueU (φ : S3.ShortMaps F G) : F.obj (iio 2) → G.obj (iio 2) :=
  hF.glue U2 U2_cover (U2Family φ) (U2Family_compat φ)

theorem K1_le_U : S3.K 1 ≤ iio 2 := (S3.K_le_J_castSucc 1).trans (U2_le 1)

/-- Fringe-gap naturality at `K 1 ≤ U`. `K 1` is not the overlap of the two stars selected for
`U` (that overlap is `K 0`). The square uses the glue computation at the member `J 1`, the left
incidence equation of edge `1`, and thinness of `G`. -/
theorem fringe_square_U (φ : S3.ShortMaps F G) (x : F.obj (S3.K 1)) :
    G.map (homOfLE K1_le_U) (φ.gap 1 x) = glueU hF φ (F.map (homOfLE K1_le_U) x) := by
  have hK : S3.K 1 ≤ U2 1 := S3.K_le_J_castSucc 1
  unfold glueU
  rw [← map_map_apply_of_thin F (homOfLE hK) (homOfLE (U2_le 1)) (homOfLE K1_le_U) x,
    hF.glue_map (1 : Fin 2)]
  exact (map_map_apply_of_thin G (homOfLE hK) (homOfLE (U2_le 1)) (homOfLE K1_le_U)
    (φ.gap 1 x)).symm.trans (congrArg (G.map (homOfLE (U2_le 1))) (φ.left_comm 1 x))

/-- The general fringe-gap dichotomy at `K 1 ≤ (-∞, 2)`. -/
example : iio 2 = S3.K 1 ∨ S3.J (1 : Fin 2).castSucc ≤ iio 2 ∨ S3.J (1 : Fin 2).succ ≤ iio 2 :=
  S3.K_le_envelope_cases S3_envelope_U K1_le_U

/-- A strict refinement of the two-star cover of `U`: `(-∞, 1/2)` and `J 1`. -/
def Isrc : Fin 2 → OpenInterval := ![iio (1 / 2), S3.J 1]

theorem Isrc_cover : ⋃ k, (Isrc k : Set ℝ) = iio 2 := by
  ext x
  rw [mem_iUnion, Fin.exists_fin_two]
  show x ∈ iio (1 / 2) ∨ x ∈ S3.J 1 ↔ x ∈ iio 2
  rw [S3_J1, mem_iio, mem_ioo, mem_iio]
  constructor
  · rintro (h | ⟨-, h⟩) <;> linarith
  · intro h
    by_cases h₁ : x < 1 / 2
    · exact Or.inl h₁
    · exact Or.inr ⟨by linarith, h⟩

theorem Isrc_le (k : Fin 2) : Isrc k ≤ U2 k := by
  fin_cases k
  · show iio (1 / 2) ≤ S3.J 0
    rw [S3_J0]
    exact OpenInterval.le_iff_subset.2 fun x hx =>
      show x < 1 from lt_trans (mem_iio.1 hx) (by norm_num)
  · exact le_rfl

/-- The first refining member is a strict subinterval of its star. -/
theorem Isrc_lt : Isrc 0 < U2 0 := by
  refine (Isrc_le 0).lt_of_ne fun h => ?_
  have h₁ : (3 / 4 : ℝ) ∈ U2 0 := by
    show (3 / 4 : ℝ) ∈ S3.J 0
    rw [S3_J0, mem_iio]; norm_num
  rw [← h] at h₁
  exact absurd (mem_iio.1 (show (3 / 4 : ℝ) ∈ iio (1 / 2) from h₁)) (by norm_num)

/-- The refined family, pulled back from the two-star family. -/
def IsrcFamily (φ : S3.ShortMaps F G) (k : Fin 2) : F.obj (Isrc k) → G.obj (iio 2) :=
  fun x => U2Family φ k (F.map (homOfLE (Isrc_le k)) x)

theorem IsrcFamily_compat (φ : S3.ShortMaps F G) (k l : Fin 2) (c : F.obj (Isrc k ⊓ Isrc l)) :
    IsrcFamily φ k (F.map (homOfLE inf_le_left) c) =
      IsrcFamily φ l (F.map (homOfLE inf_le_right) c) :=
  compat_comp id Isrc_le (U2Family φ) (U2Family_compat φ) k l c

/-- Gluing over the strict refinement agrees with gluing over the selected stars of `U`. -/
theorem glueIsrc_eq (φ : S3.ShortMaps F G) (x : F.obj (iio 2)) :
    hF.glue Isrc Isrc_cover (IsrcFamily φ) (IsrcFamily_compat φ) x = glueU hF φ x :=
  (hF.glue_comp_map (hJ := Isrc_cover) (a := IsrcFamily φ) (ha := IsrcFamily_compat φ)
    (hH := U2_cover) (b := U2Family φ) (hb := U2Family_compat φ) (le_rfl : iio 2 ≤ iio 2)
    (id : Fin 2 → Fin 2) Isrc_le id (fun _ _ => rfl) x).trans (congrArg _ (map_self_apply _ x))

/-- Cover comparison with a multi-member source cover, a strict member inclusion and the
non-constant index map `Fin.castSucc : Fin 2 → Fin 3`, into the three-star cover of `⊤`. -/
theorem glueIsrc_comp_map (φ : S3.ShortMaps F G) (x : F.obj (iio 2)) :
    G.map (homOfLE le_top) (hF.glue Isrc Isrc_cover (IsrcFamily φ) (IsrcFamily_compat φ) x) =
      glueTop hF φ (F.map (homOfLE le_top) x) :=
  hF.glue_comp_map (hJ := Isrc_cover) (a := IsrcFamily φ) (ha := IsrcFamily_compat φ)
    (hH := S3_cover) (b := starFamily φ) (hb := starFamily_compat hF.isEmpty_obj_bot φ)
    (le_top : iio 2 ≤ ⊤) Fin.castSucc Isrc_le (G.map (homOfLE le_top))
    (fun k e => map_map_apply_of_thin G (homOfLE (U2_le k)) (homOfLE le_top) (homOfLE le_top)
      (φ.star k.castSucc (F.map (homOfLE (Isrc_le k)) e))) x

/-- Cover universe: the same star cover indexed by `ULift.{w} (Fin 3)` under
`IsIntervalCosheaf.{w}`, values in an independent universe `u`. -/
theorem S3_cover_ulift : ⋃ k : ULift.{w} (Fin 3), (S3.J k.down : Set ℝ) = (⊤ : OpenInterval) :=
  (Equiv.ulift.surjective.iUnion_comp (fun i => (S3.J i : Set ℝ))).trans S3_cover

example (hF' : IsIntervalCosheaf.{w} F) (φ : S3.ShortMaps F G) :
    ∃! g : F.obj ⊤ → G.obj ⊤, ∀ (k : ULift.{w} (Fin 3)) (e : F.obj (S3.J k.down)),
      g (F.map (homOfLE (le_of_iUnion_eq S3_cover_ulift.{w} k)) e) = starFamily φ k.down e :=
  hF'.existsUnique_glue (fun k : ULift.{w} (Fin 3) => S3.J k.down) S3_cover_ulift.{w}
    (fun k => starFamily φ k.down)
    (fun k l c => starFamily_compat hF'.isEmpty_obj_bot φ k.down l.down c)

end threeLevel

/-! ### Finite data fixtures: empty values, parallel edges, noninjective attachments -/

section data

/-- Zero data (all values empty). -/
def zeroData (n : ℕ) : FiniteReebData.{0} n :=
  ⟨fun _ => Empty, fun _ => Empty, fun _ => inferInstance, fun _ => inferInstance,
    fun _ x => x.elim, fun _ x => x.elim⟩

/-- Empty edges with nonempty isolated vertices. -/
def isolatedData (n : ℕ) : FiniteReebData.{0} n :=
  ⟨fun _ => Unit, fun _ => Empty, fun _ => inferInstance, fun _ => inferInstance,
    fun _ x => x.elim, fun _ x => x.elim⟩

/-- Two parallel edges between levels: injective on the left, noninjective on the right
(both attach to `true`; `false` on the right is isolated). -/
def pinchData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Bool, fun _ => Bool, fun _ => inferInstance, fun _ => inferInstance,
    fun _ x => x, fun _ _ => true⟩

theorem pinchData_right_not_injective : ¬ Function.Injective (pinchData.right 0) :=
  fun h => Bool.false_ne_true (h rfl)

/-- Collapse onto a single edge: a noninjective finite map. -/
def pointData : FiniteReebData.{0} 1 :=
  ⟨fun _ => Unit, fun _ => Unit, fun _ => inferInstance, fun _ => inferInstance,
    fun _ _ => (), fun _ _ => ()⟩

/-- The collapse of the parallel edges onto one edge. -/
def collapseHom : pinchData.Hom pointData :=
  ⟨fun _ _ => (), fun _ _ => (), fun _ _ => rfl, fun _ _ => rfl⟩

theorem collapseHom_e_not_injective : ¬ Function.Injective (collapseHom.e 0) :=
  fun h => Bool.false_ne_true (h rfl)

/-- Swap the left vertex and the edges, fixing the right vertices. -/
def swapHom : pinchData.Hom pinchData where
  v i := if i = 0 then (! ·) else _root_.id
  e _ := (! ·)
  left_comm i x := by fin_cases i; rfl
  right_comm i x := by fin_cases i; rfl

theorem swapHom_bijective_v (i : Fin 2) : Function.Bijective (swapHom.v i) := by
  fin_cases i
  · exact Function.Involutive.bijective (f := (! ·)) Bool.not_not
  · exact Function.bijective_id

theorem swapHom_bijective_e (e : Fin 1) : Function.Bijective (swapHom.e e) :=
  Function.Involutive.bijective (f := (! ·)) Bool.not_not

/-- The inverse built from component bijections is a two-sided inverse. -/
example : swapHom.comp (swapHom.inv swapHom_bijective_v swapHom_bijective_e) =
    FiniteReebData.Hom.id pinchData :=
  swapHom.comp_inv _ _

example : (swapHom.inv swapHom_bijective_v swapHom_bijective_e).comp swapHom =
    FiniteReebData.Hom.id pinchData :=
  swapHom.inv_comp _ _

end data

/-! ### The strip `A × [0, 2] → ℝ` -/

section strip

/-- Projection `A × [0, 2] → ℝ`. -/
def strip (A : Type u) [TopologicalSpace A] : C(A × Icc (0 : ℝ) 2, ℝ) :=
  ⟨fun p => (p.2 : ℝ), by fun_prop⟩

variable (A : Type u) [TopologicalSpace A]

example : IsIntervalCosheaf.{w} (intervalComponents (strip A)) :=
  intervalComponents_isIntervalCosheaf _

/-- Nonempty regular value. -/
theorem strip_regular_nonempty [Nonempty A] :
    Nonempty ((intervalComponents (strip A)).obj (ioo 0 2)) :=
  ⟨ZerothHomotopy.mk ⟨(Classical.arbitrary A, ⟨1, by norm_num, by norm_num⟩),
    show (1 : ℝ) ∈ Ioo 0 2 by norm_num⟩⟩

example : IsEmpty ((intervalComponents (strip A)).obj ⊥) := inferInstance

/-- Empty lower exterior value. -/
theorem strip_lower_empty : IsEmpty ((intervalComponents (strip A)).obj (iio 0)) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact absurd (show ((x.1.2 : ℝ)) < 0 from x.2) (not_lt.2 x.1.2.2.1)⟩

/-- Empty upper exterior value. -/
theorem strip_upper_empty : IsEmpty ((intervalComponents (strip A)).obj (ioi 2)) :=
  ⟨fun c => by
    induction c using ZerothHomotopy.rec with
    | mk x => exact absurd (show (2 : ℝ) < x.1.2 from x.2) (not_lt.2 x.1.2.2.2)⟩

/-- Critical values `0 < 2` for the strip. -/
def S2 : CriticalValues 1 := ⟨![0, 2], Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; simp⟩

theorem S2_value_zero : S2.value 0 = 0 := rfl
theorem S2_value_one : S2.value 1 = 2 := rfl

theorem S2_K0 : S2.K 0 = ioo 0 2 := by simp [CriticalValues.K, S2]

theorem S2_lowerTail : S2.lowerTail = iio 0 := by simp [CriticalValues.lowerTail, S2]
theorem S2_upperTail : S2.upperTail = ioi 2 := by simp [CriticalValues.upperTail, S2]

/-- Endpoint computation: the stars of `S2` are `(-∞, 2)` and `(0, ∞)`. -/
theorem S2_J0 : S2.J 0 = iio 2 := by
  have h₂ : S2.upperCut 0 = ((2 : ℝ) : EReal) := by
    rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from rfl, S2.upperCut_castSucc]; simp [S2]
  ext x
  rw [S2.mem_J, CriticalValues.lowerCut_zero, h₂, mem_iio, EReal.coe_lt_coe_iff]
  exact ⟨fun h => h.2, fun h => ⟨EReal.bot_lt_coe x, h⟩⟩

theorem S2_J1 : S2.J 1 = ioi 0 := by
  have h₁ : S2.lowerCut 1 = ((0 : ℝ) : EReal) := by
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, S2.lowerCut_succ]; simp [S2]
  have h₂ : S2.upperCut 1 = ⊤ := S2.upperCut_last
  ext x
  rw [S2.mem_J, h₁, h₂, mem_ioi, EReal.coe_lt_coe_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, EReal.coe_lt_top x⟩⟩

/-- The strip's empty exterior values are exactly the tails of `S2`. -/
theorem strip_isEmpty_S2_lowerTail :
    IsEmpty ((intervalComponents (strip A)).obj S2.lowerTail) := by
  rw [S2_lowerTail]; exact strip_lower_empty A

theorem strip_isEmpty_S2_upperTail :
    IsEmpty ((intervalComponents (strip A)).obj S2.upperTail) := by
  rw [S2_upperTail]; exact strip_upper_empty A

/-- The uncorrected rule (no nonempty source) fails: `⊥ ≤ K 0` meets the same levels (none),
yet `F ⊥ → F (K 0)` is not bijective since its target is nonempty. -/
theorem uncorrected_rule_fails :
    ¬ ∀ ⦃I J : OpenInterval⦄ (h : I ≤ J), (∀ i, S2.value i ∈ I ↔ S2.value i ∈ J) →
      Function.Bijective ((intervalComponents (strip PUnit.{1})).map (homOfLE h)) := by
  intro hrule
  have hhit : ∀ i, S2.value i ∈ (⊥ : OpenInterval) ↔ S2.value i ∈ S2.K 0 :=
    fun i => iff_of_false (fun h => h) (S2.value_notMem_K 0 i)
  obtain ⟨y⟩ := strip_regular_nonempty PUnit.{1}
  rw [← S2_K0] at y
  obtain ⟨x, -⟩ := (hrule (bot_le : ⊥ ≤ S2.K 0) hhit).2 y
  exact (intervalComponents_obj_bot_isEmpty _).false x

variable [DiscreteTopology A]

/-- First coordinate of a component of the strip of a discrete space. -/
def firstCoord (I : OpenInterval) : (intervalComponents (strip A)).obj I → A :=
  ZerothHomotopy.lift (fun x => x.1.1) fun _ _ p =>
    eq_of_joined_of_discrete ⟨p.map (by fun_prop :
      Continuous fun x : {x : A × Icc (0 : ℝ) 2 // strip A x ∈ toOpens I} => x.1.1)⟩

theorem firstCoord_mk (I : OpenInterval) (x : {x : A × Icc (0 : ℝ) 2 // strip A x ∈ toOpens I}) :
    firstCoord A I (ZerothHomotopy.mk x) = x.1.1 := rfl

omit [DiscreteTopology A] in
/-- Points with the same first coordinate lie in one component: the fibre over the first
coordinate is the image of the convex set `I ∩ [0, 2]`. -/
theorem strip_mk_eq_mk {I : OpenInterval} (x y : {x : A × Icc (0 : ℝ) 2 // strip A x ∈ toOpens I})
    (h : x.1.1 = y.1.1) :
    (ZerothHomotopy.mk x : (intervalComponents (strip A)).obj I) = ZerothHomotopy.mk y := by
  have hconv : Convex ℝ ((I : Set ℝ) ∩ Icc 0 2) :=
    (convex_iff_ordConnected.2 I.ordConnected).inter (convex_Icc 0 2)
  have hpc := (hconv.isPathConnected ⟨_, x.2, x.1.2.2⟩).image
    (show Continuous fun t : ℝ => (x.1.1, projIcc (0 : ℝ) 2 (by norm_num) t) by
      exact continuous_const.prodMk continuous_projIcc)
  have hx : (x.1.1, projIcc (0 : ℝ) 2 (by norm_num) (x.1.2 : ℝ)) = x.1 := by
    rw [projIcc_val]
  have hy : (x.1.1, projIcc (0 : ℝ) 2 (by norm_num) (y.1.2 : ℝ)) = y.1 := by
    rw [projIcc_val, h]
  have hJ := hpc.joinedIn _ ⟨_, ⟨x.2, x.1.2.2⟩, hx⟩ _ ⟨_, ⟨y.2, y.1.2.2⟩, hy⟩
  have hJ' : JoinedIn {p : A × Icc (0 : ℝ) 2 | strip A p ∈ toOpens I} x.1 y.1 :=
    hJ.mono (by
      rintro _ ⟨t, ⟨htI, htc⟩, rfl⟩
      show ((projIcc (0 : ℝ) 2 (by norm_num) t : Icc (0 : ℝ) 2) : ℝ) ∈ I
      rwa [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 2) htc])
  exact Quotient.sound hJ'.joined_subtype

theorem firstCoord_injective (I : OpenInterval) : Function.Injective (firstCoord A I) := by
  intro c d h
  induction c using ZerothHomotopy.rec with
  | mk x =>
    induction d using ZerothHomotopy.rec with
    | mk y => exact strip_mk_eq_mk A x y h

theorem firstCoord_map {I J : OpenInterval} (h : I ≤ J)
    (c : (intervalComponents (strip A)).obj I) :
    firstCoord A J ((intervalComponents (strip A)).map (homOfLE h) c) = firstCoord A I c := by
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- If `I ≤ J` meet the same levels of `S2` and `I` is nonempty, then `I` meets `[0, 2]` as soon
as `J` does. -/
theorem exists_mem_Icc_of_hits {I J : OpenInterval} (hIJ : I ≤ J) (hI : (I : Set ℝ).Nonempty)
    (hhit : ∀ i, S2.value i ∈ I ↔ S2.value i ∈ J) {t : ℝ} (htJ : t ∈ J)
    (ht : t ∈ Icc (0 : ℝ) 2) : ∃ s ∈ I, s ∈ Icc (0 : ℝ) 2 := by
  have h0 := hhit 0
  have h2 := hhit 1
  rw [S2_value_zero] at h0
  rw [S2_value_one] at h2
  by_cases hI0 : (0 : ℝ) ∈ I
  · exact ⟨0, hI0, by norm_num, by norm_num⟩
  by_cases hI2 : (2 : ℝ) ∈ I
  · exact ⟨2, hI2, by norm_num, by norm_num⟩
  obtain ⟨y, hy⟩ := hI
  refine ⟨y, hy, ?_, ?_⟩
  · by_contra hlt
    exact hI0 (h0.2 (mem_of_le_of_le (hIJ hy) htJ (not_le.1 hlt).le ht.1))
  · by_contra hlt
    exact hI2 (h2.2 (mem_of_le_of_le htJ (hIJ hy) ht.2 (not_le.1 hlt).le))

/-- The strip of a finite discrete space satisfies the corrected predicate at `{0, 2}`. -/
theorem strip_isConstructibleAt [Finite A] :
    S2.IsConstructibleAt (intervalComponents (strip A)) where
  finite I := Finite.of_injective _ (firstCoord_injective A I)
  bijective I J h hI hhit := by
    refine ⟨fun c d hcd => firstCoord_injective A I ?_, fun d => ?_⟩
    · rw [← firstCoord_map A h c, ← firstCoord_map A h d, hcd]
    · induction d using ZerothHomotopy.rec with
      | mk y =>
        obtain ⟨s, hsI, hs⟩ := exists_mem_Icc_of_hits h hI hhit (t := (y.1.2 : ℝ)) y.2 y.1.2.2
        exact ⟨ZerothHomotopy.mk ⟨(y.1.1, ⟨s, hs⟩), hsI⟩, strip_mk_eq_mk A _ y rfl⟩
  isEmpty_lowerTail := strip_isEmpty_S2_lowerTail A
  isEmpty_upperTail := strip_isEmpty_S2_upperTail A

end strip

/-- The point strip satisfies the corrected predicate at `{0, 2}` and refutes the uncorrected
rule. -/
theorem strip_corrected_not_uncorrected :
    S2.IsConstructibleAt (intervalComponents (strip PUnit.{1})) ∧
      ¬ ∀ ⦃I J : OpenInterval⦄ (h : I ≤ J), (∀ i, S2.value i ∈ I ↔ S2.value i ∈ J) →
        Function.Bijective ((intervalComponents (strip PUnit.{1})).map (homOfLE h)) :=
  ⟨strip_isConstructibleAt PUnit.{1}, uncorrected_rule_fails⟩

/-- Endpoint computation: the left endpoint function of the extracted data of the point strip
is the actual inclusion map on representatives. -/
theorem strip_extract_left_mk
    (x : {x : PUnit.{1} × Icc (0 : ℝ) 2 // strip PUnit.{1} x ∈ toOpens (S2.K 0)}) :
    (S2.extract (intervalComponents (strip PUnit.{1}))
      (strip_isConstructibleAt PUnit.{1}).finite).left 0 (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk ⟨x.1, OpenInterval.le_iff_subset.1 (S2.K_le_J_castSucc 0) x.2⟩ :=
  rfl

/-- The extracted data of the point strip at `S2`: one vertex at each level, one edge, and both
endpoint functions bijective. -/
theorem strip_extract_bijective :
    Function.Bijective ((S2.extract (intervalComponents (strip PUnit.{1}))
      (strip_isConstructibleAt PUnit.{1}).finite).left 0) ∧
    Function.Bijective ((S2.extract (intervalComponents (strip PUnit.{1}))
      (strip_isConstructibleAt PUnit.{1}).finite).right 0) := by
  have hsub : ∀ I, Subsingleton ((intervalComponents (strip PUnit.{1})).obj I) := fun I =>
    ⟨fun a b => firstCoord_injective PUnit.{1} I (Subsingleton.elim _ _)⟩
  have hK : Nonempty ((intervalComponents (strip PUnit.{1})).obj (S2.K 0)) := by
    rw [S2_K0]; exact strip_regular_nonempty PUnit.{1}
  exact ⟨@bijective_of_subsingleton _ _ (hsub _) (hsub _) _ fun _ => hK,
    @bijective_of_subsingleton _ _ (hsub _) (hsub _) _ fun _ => hK⟩

/-! ### A transformation merging two regular components -/

/-- The two components over `(0, 2)` of the `Bool` strip. -/
def boolClass (b : Bool) : (intervalComponents (strip Bool)).obj (ioo 0 2) :=
  ZerothHomotopy.mk ⟨(b, ⟨1, by norm_num, by norm_num⟩), show (1 : ℝ) ∈ Ioo 0 2 by norm_num⟩

theorem boolClass_ne : boolClass false ≠ boolClass true := fun h =>
  Bool.false_ne_true (congrArg (firstCoord Bool (ioo 0 2)) h)

/-- The collapse `Bool × [0,2] → PUnit × [0,2]` over the base, on interval components. -/
def collapse : intervalComponents (strip Bool) ⟶ intervalComponents (strip PUnit.{1}) :=
  Functor.whiskerLeft toOpensFunctor
    (componentNatTrans (f := strip Bool) (g := strip PUnit.{1})
      ⟨fun p => (PUnit.unit, p.2), by fun_prop⟩ (fun _ => rfl))

/-- The collapse merges two regular components. -/
theorem collapse_not_injective : ¬ Function.Injective (collapse.app (ioo 0 2)) :=
  fun h => boolClass_ne (h rfl)

/-- The collapse is not an isomorphism: its gap component over `(0, 2)` is not injective, so the
short-interval criterion fails. -/
theorem collapse_not_isIso : ¬ IsIso collapse := fun h => by
  have := ((S2.isIso_iff_shortIntervals (strip_isConstructibleAt Bool)
    (intervalComponents_isIntervalCosheaf _) (strip_isConstructibleAt PUnit.{1})
    (intervalComponents_isIntervalCosheaf _) collapse).1 h).2 0
  rw [S2_K0] at this
  exact collapse_not_injective this.1

/-- The collapse is determined by its star and gap components. -/
example (β : intervalComponents (strip Bool) ⟶ intervalComponents (strip PUnit.{1}))
    (hJ : ∀ i x, collapse.app (S2.J i) x = β.app (S2.J i) x)
    (hK : ∀ e x, collapse.app (S2.K e) x = β.app (S2.K e) x) : collapse = β :=
  S2.natTrans_ext (strip_isConstructibleAt Bool) (intervalComponents_isIntervalCosheaf _)
    (strip_isConstructibleAt PUnit.{1}) (intervalComponents_isIntervalCosheaf _) hJ hK

/-- Extending the identity short maps gives the identity. -/
example : (S2.natTransEquivShortMaps (strip_isConstructibleAt PUnit.{1})
    (intervalComponents_isIntervalCosheaf _) (strip_isConstructibleAt PUnit.{1})
    (intervalComponents_isIntervalCosheaf _)).symm (CriticalValues.ShortMaps.id _) = 𝟙 _ :=
  (Equiv.symm_apply_eq _).2 (S2.restrict_id _).symm

/-! ### Refinement `{0, 2} → {0, 1, 2}` and distinct gap values -/

theorem S2_refines_S3 : Set.range S2.value ⊆ Set.range S3.value := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- The strip stays constructible after refining `{0, 2}` to `{0, 1, 2}`. -/
theorem strip_isConstructibleAt_S3 (A : Type u) [TopologicalSpace A] [DiscreteTopology A]
    [Finite A] : S3.IsConstructibleAt (intervalComponents (strip A)) :=
  (strip_isConstructibleAt A).of_refines S2_refines_S3

/-- Refinement shrinks the envelope: `(1/4, 3/4)` has envelope `(0, 1)` for `{0, 1, 2}` and
`(0, 2)` for `{0, 2}`. -/
theorem envelope_refinement :
    S3.envelope (ioo (1 / 4) (3 / 4)) = ioo 0 1 ∧ S2.envelope (ioo (1 / 4) (3 / 4)) = ioo 0 2 ∧
      ioo 0 1 < ioo 0 2 := by
  have hne : ((ioo (1 / 4) (3 / 4) : OpenInterval) : Set ℝ).Nonempty :=
    ⟨1 / 2, mem_ioo.2 ⟨by norm_num, by norm_num⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← S3_K0]
    exact S3.envelope_eq_K (by
      rw [S3_K0]; exact fun x hx => mem_ioo.2 ⟨by linarith [(mem_ioo.1 hx).1],
        by linarith [(mem_ioo.1 hx).2]⟩) hne
  · rw [← S2_K0]
    exact S2.envelope_eq_K (by
      rw [S2_K0]; exact fun x hx => mem_ioo.2 ⟨by linarith [(mem_ioo.1 hx).1],
        by linarith [(mem_ioo.1 hx).2]⟩) hne
  · refine lt_of_le_of_ne (fun x hx => mem_ioo.2 ⟨(mem_ioo.1 hx).1,
      by linarith [(mem_ioo.1 hx).2]⟩) fun h => ?_
    have : (3 / 2 : ℝ) ∈ ioo 0 2 := mem_ioo.2 ⟨by norm_num, by norm_num⟩
    rw [← h] at this
    exact absurd (mem_ioo.1 this).2 (by norm_num)

/-- Critical values `0 < 2 < 3`. -/
def S023 : CriticalValues 2 :=
  ⟨![0, 2, 3], Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i <;> simp [show (2 : ℝ) < 3 by norm_num]⟩

theorem S2_refines_S023 : Set.range S2.value ⊆ Set.range S023.value := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem S023_K0 : S023.K 0 = ioo 0 2 := by simp [CriticalValues.K, S023]
theorem S023_K1 : S023.K 1 = ioo 2 3 := by simp [CriticalValues.K, S023]

/-- Two distinct regular gaps meet no level, yet the strip, constructible at `{0, 2, 3}`, has a
nonempty value on `(0, 2)` and an empty value on `(2, 3)`: equal critical hits do not identify
values on non-nested intervals. -/
theorem distinct_gap_values :
    S023.IsConstructibleAt (intervalComponents (strip PUnit.{1})) ∧
      (∀ i, S023.value i ∉ S023.K 0 ∧ S023.value i ∉ S023.K 1) ∧
      Nonempty ((intervalComponents (strip PUnit.{1})).obj (S023.K 0)) ∧
      IsEmpty ((intervalComponents (strip PUnit.{1})).obj (S023.K 1)) ∧
      ¬ Nonempty ((intervalComponents (strip PUnit.{1})).obj (S023.K 0) ≃
        (intervalComponents (strip PUnit.{1})).obj (S023.K 1)) := by
  have h₀ : Nonempty ((intervalComponents (strip PUnit.{1})).obj (S023.K 0)) := by
    rw [S023_K0]; exact strip_regular_nonempty PUnit.{1}
  have hle : S023.K 1 ≤ ioi 2 := by
    rw [S023_K1]; exact fun x hx => mem_ioi.2 (mem_ioo.1 hx).1
  have h₁ : IsEmpty ((intervalComponents (strip PUnit.{1})).obj (S023.K 1)) :=
    ⟨fun c => (strip_upper_empty PUnit.{1}).false
      ((intervalComponents (strip PUnit.{1})).map (homOfLE hle) c)⟩
  exact ⟨(strip_isConstructibleAt PUnit.{1}).of_refines S2_refines_S023,
    fun i => ⟨S023.value_notMem_K 0 i, S023.value_notMem_K 1 i⟩, h₀, h₁,
    fun ⟨e⟩ => h₁.false (e h₀.some)⟩

end

end TDA.Reeb.Examples.Constructible
