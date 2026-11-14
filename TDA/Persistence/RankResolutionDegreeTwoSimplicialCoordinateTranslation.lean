import TDA.Persistence.RankResolutionDegreeTwoSimplicialTranslation

/-!
# Exact distance between independent coordinate translates of the simplicial witness

Each face coordinate may be delayed by its own signed real amount.  The
resulting actual degree-one homology is a reindexing of the original module;
its optimal coordinatewise interleaving distance is the largest coordinate
displacement, capped by half of the diagonal lifetime.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.RankResolutionDegreeTwoSimplicial

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open RankResolutionDegreeTwo
open scoped TDA.Persistence NNReal ENNReal

/-- Pull back each parameter coordinate by its own signed face delay. -/
def coordinateTranslationPullback (v : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →o (Fin 2 → ℝ) :=
  OrderHomClass.toOrderHom (OrderIso.addRight (fun i : Fin 2 => -v i))

@[simp] theorem coordinateTranslationPullback_apply (v p : Fin 2 → ℝ) (i : Fin 2) :
    coordinateTranslationPullback v p i = p i - v i := rfl

/-- Translate each actual face grade by an independent signed coordinate vector. -/
def coordinateTranslatedGrading (v : Fin 2 → ℝ) : FiniteGraded boundaryTetrahedron 2 where
  grade σ i := boundaryTetrahedronGrading.grade σ i + v i
  mono h i := by
    have hg := boundaryTetrahedronGrading.mono h i
    dsimp only
    linarith

@[simp] theorem coordinateTranslatedGrading_grade (v : Fin 2 → ℝ)
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    (coordinateTranslatedGrading v).grade σ i =
      boundaryTetrahedronGrading.grade σ i + v i := rfl

@[simp] theorem coordinateTranslatedGrading_zero :
    coordinateTranslatedGrading (0 : Fin 2 → ℝ) = boundaryTetrahedronGrading := by
  apply FiniteGraded.ext
  intro σ
  funext i
  simp

/-- A constant vector recovers the established scalar grading exactly. -/
theorem coordinateTranslatedGrading_const (t : ℝ) :
    coordinateTranslatedGrading (fun _ : Fin 2 => t) = translatedGrading t := by
  apply FiniteGraded.ext
  intro σ
  funext i
  rfl

/-- The face sublevel set is the original sublevel set at the coordinate pullback. -/
theorem coordinateTranslatedGrading_sublevel (v : Fin 2 → ℝ) (p : Fin 2 → ℝ) :
    (coordinateTranslatedGrading v).sublevel p =
      boundaryTetrahedronGrading.sublevel (coordinateTranslationPullback v p) := by
  apply le_antisymm
  · rintro σ ⟨hσ, hp⟩
    exact ⟨hσ, fun i => le_sub_iff_add_le.mpr (hp i)⟩
  · rintro σ ⟨hσ, hp⟩
    exact ⟨hσ, fun i => le_sub_iff_add_le.mp (hp i)⟩

/-- Actual inclusion-induced degree-one homology of the independently translated input. -/
noncomputable abbrev coordinateTranslatedHomology (k : Type u) [Field k]
    (v : Fin 2 → ℝ) : PModule.{u,0,u} k (Fin 2 → ℝ) :=
  finiteSimplicialHomology k (coordinateTranslatedGrading v) 1

@[simp] theorem coordinateTranslatedHomology_zero (k : Type u) [Field k] :
    coordinateTranslatedHomology k (0 : Fin 2 → ℝ) =
      finiteSimplicialHomology k boundaryTetrahedronGrading 1 := by
  simp only [coordinateTranslatedHomology, coordinateTranslatedGrading_zero]

/-- Constant-vector translation agrees with the existing scalar module. -/
theorem coordinateTranslatedHomology_const (k : Type u) [Field k] (t : ℝ) :
    coordinateTranslatedHomology k (fun _ : Fin 2 => t) = translatedHomology k t := by
  simp only [coordinateTranslatedHomology, coordinateTranslatedGrading_const,
    translatedHomology]

/-- The actual translated module is naturally the pullback of the original homology. -/
noncomputable def coordinateTranslatedHomologyReindexIso (k : Type u) [Field k]
    (v : Fin 2 → ℝ) :
    coordinateTranslatedHomology k v ≅
      reindex (coordinateTranslationPullback v)
        (finiteSimplicialHomology k boundaryTetrahedronGrading 1) := by
  have hfil : (coordinateTranslatedGrading v).sublevelFiltration =
      TDA.Filtration.reindex (coordinateTranslationPullback v)
        boundaryTetrahedronGrading.sublevelFiltration := by
    apply DFunLike.ext
    intro p
    exact coordinateTranslatedGrading_sublevel v p
  unfold coordinateTranslatedHomology finiteSimplicialHomology
  rw [hfil]
  exact Iso.refl _

/-- Realization comparison in the original actual Lan, with all coordinate shifts retained. -/
noncomputable def coordinateTranslatedRealIso (k : Type u) [Field k] (v : Fin 2 → ℝ) :
    coordinateTranslatedHomology k v ≅
      reindex (coordinateTranslationPullback v) (realModule (k := k)) :=
  (coordinateTranslatedHomologyReindexIso k v).trans
    (Functor.isoWhiskerLeft (coordinateTranslationPullback v).toFunctor (realIso k))

/-- Naturality of the actual realization comparison on every structure map. -/
theorem coordinateTranslatedRealIso_structureMap (k : Type u) [Field k]
    (v : Fin 2 → ℝ) {p q : Fin 2 → ℝ} (hpq : p ≤ q) :
    structureMap (coordinateTranslatedHomology k v) hpq ≫
        (coordinateTranslatedRealIso k v).hom.app q =
      (coordinateTranslatedRealIso k v).hom.app p ≫
        structureMap (realModule (k := k))
          ((coordinateTranslationPullback v).monotone' hpq) :=
  (coordinateTranslatedRealIso k v).hom.naturality (homOfLE hpq)

/-- Finite presentation descends directly from the unchanged finite simplicial input. -/
theorem coordinateTranslatedHomology_finitelyPresented (k : Type u) [Field k]
    (v : Fin 2 → ℝ) :
    GradedFree.FinitelyPresented.{u,0,0} (R := k) (P := Fin 2 → ℝ)
      (coordinateTranslatedHomology k v) :=
  finiteSimplicialHomology_finitelyPresented k (coordinateTranslatedGrading v) 1

private noncomputable def coordinateArmBase (i : Fin 2) : Fin 2 → ℝ :=
  if i = 0 then grid.embedding a else grid.embedding b

/-- Birth index of the arm whose selected coordinate starts at zero before translation. -/
noncomputable def coordinateTranslatedBirth (i : Fin 2) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun j => coordinateArmBase i j + v j

/-- Each indexed birth has its literal boundary-arm coordinates plus the delay vector. -/
theorem coordinateTranslatedBirth_apply (i : Fin 2) (v : Fin 2 → ℝ) (j : Fin 2) :
    coordinateTranslatedBirth i v j = (if i = j then (0 : ℝ) else 1) + v j := by
  fin_cases i
  · fin_cases j
    · change grid.embedding a 0 + v 0 = 0 + v 0
      rw [grid_embedding_a]
      norm_num
    · change grid.embedding a 1 + v 1 = 1 + v 1
      rw [grid_embedding_a]
      norm_num
  · fin_cases j
    · change grid.embedding b 0 + v 0 = 1 + v 0
      rw [grid_embedding_b]
      norm_num
    · change grid.embedding b 1 + v 1 = 0 + v 1
      rw [grid_embedding_b]
      norm_num

@[simp] theorem coordinateTranslatedBirth_selected (i : Fin 2) (v : Fin 2 → ℝ) :
    coordinateTranslatedBirth i v i = v i := by
  simp [coordinateTranslatedBirth_apply]

private theorem coordinateTranslationPullback_birth (i : Fin 2) (v : Fin 2 → ℝ) :
    coordinateTranslationPullback v (coordinateTranslatedBirth i v) = coordinateArmBase i := by
  funext j
  simp [coordinateTranslationPullback_apply, coordinateTranslatedBirth, coordinateArmBase]

private theorem coordinateTranslationPullback_birth_step (i : Fin 2) (v : Fin 2 → ℝ)
    (r : ℝ) :
    coordinateTranslationPullback v (fun j => coordinateTranslatedBirth i v j + r) =
      fun j => coordinateArmBase i j + r := by
  funext j
  simp only [coordinateTranslationPullback_apply, coordinateTranslatedBirth,
    coordinateArmBase]
  ring

private theorem coordinateMap_zero_of_iso {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} (e : M ≅ N)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hz : structureMap N hpq = 0) :
    structureMap M hpq = 0 := by
  apply (cancel_mono (e.hom.app q)).mp
  have hn := e.hom.naturality (homOfLE hpq)
  change structureMap M hpq ≫ e.hom.app q = e.hom.app p ≫ structureMap N hpq at hn
  rw [hn, hz, comp_zero, zero_comp]

private theorem coordinateMap_ne_zero_of_iso {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} (e : M ≅ N)
    {p q : Fin 2 → ℝ} (hpq : p ≤ q) (hne : structureMap N hpq ≠ 0) :
    structureMap M hpq ≠ 0 := by
  intro hz
  exact hne (coordinateMap_zero_of_iso e.symm hpq hz)

private theorem structureMap_zero_of_module_index_eq {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} {p p' q q' : Fin 2 → ℝ}
    (hM : M = N) (hp : p = p') (hq : q = q') {h : p ≤ q} {h' : p' ≤ q'}
    (hz : structureMap N h' = 0) : structureMap M h = 0 := by
  cases hM
  cases hp
  cases hq
  exact hz

private theorem structureMap_ne_zero_of_module_index_eq {k : Type u} [Field k]
    {M N : PModule.{u,0,u} k (Fin 2 → ℝ)} {p p' q q' : Fin 2 → ℝ}
    (hM : M = N) (hp : p = p') (hq : q = q') {h : p ≤ q} {h' : p' ≤ q'}
    (hne : structureMap N h' ≠ 0) : structureMap M h ≠ 0 := by
  intro hz
  exact hne (structureMap_zero_of_module_index_eq hM.symm hp.symm hq.symm hz)

/-- Below any translated coordinate birth, that actual fiber is zero. -/
theorem coordinateTranslatedHomology_isZero_of_coordinate_lt (k : Type u) [Field k]
    (v : Fin 2 → ℝ) (i : Fin 2) (p : Fin 2 → ℝ) (hp : p i < v i) :
    IsZero ((coordinateTranslatedHomology k v).obj p) := by
  have hpull : (coordinateTranslationPullback v p) i < 0 := by
    simp only [coordinateTranslationPullback_apply]
    linarith
  have hz : IsZero
      ((finiteSimplicialHomology k boundaryTetrahedronGrading 1).obj
        (coordinateTranslationPullback v p)) := by
    fin_cases i
    · have h := translatedHomology_isZero_of_first_lt k 0
        (coordinateTranslationPullback v p) (by simpa using hpull)
      simpa only [translatedHomology_zero] using h
    · exact homology_isZero_of_second_neg k (coordinateTranslationPullback v p) hpull
  exact IsZero.of_iso hz ((coordinateTranslatedHomologyReindexIso k v).app p)

/-- The actual indexed arm map survives all nonnegative steps below one. -/
theorem coordinateTranslatedHomology_birth_structureMap_ne_zero (k : Type u) [Field k]
    (v : Fin 2 → ℝ) (i : Fin 2) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    structureMap (coordinateTranslatedHomology k v)
      (show coordinateTranslatedBirth i v ≤
        (fun j => coordinateTranslatedBirth i v j + r) from
          fun _ => le_add_of_nonneg_right hr0) ≠ 0 := by
  let hpq : coordinateTranslatedBirth i v ≤
      (fun j => coordinateTranslatedBirth i v j + r) :=
    fun _ => le_add_of_nonneg_right hr0
  apply coordinateMap_ne_zero_of_iso (coordinateTranslatedHomologyReindexIso k v) hpq
  rw [structureMap_reindex]
  have hbase := coordinateTranslationPullback_birth i v
  have hstep := coordinateTranslationPullback_birth_step i v r
  fin_cases i
  · have hp : coordinateTranslationPullback v (coordinateTranslatedBirth 0 v) =
        translatedBirth 0 := by
      calc
        _ = coordinateArmBase 0 := hbase
        _ = translatedBirth 0 := by
          unfold translatedBirth
          funext j
          simp [coordinateArmBase]
    have hq : coordinateTranslationPullback v
        (fun j => coordinateTranslatedBirth 0 v j + r) =
        (fun j => translatedBirth 0 j + r) := by
      calc
        _ = fun j => coordinateArmBase 0 j + r := hstep
        _ = fun j => translatedBirth 0 j + r := by
          funext j
          simp [coordinateArmBase, translatedBirth]
    exact structureMap_ne_zero_of_module_index_eq
      (M := finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      (N := translatedHomology k 0) (translatedHomology_zero k).symm hp hq
      (hne := translatedHomology_birth_structureMap_ne_zero k 0 r hr0 hr1)
  · have hp : coordinateTranslationPullback v (coordinateTranslatedBirth 1 v) =
        grid.embedding b := by
      calc
        _ = coordinateArmBase 1 := hbase
        _ = grid.embedding b := by simp [coordinateArmBase]
    have hq : coordinateTranslationPullback v
        (fun j => coordinateTranslatedBirth 1 v j + r) =
        (fun j => grid.embedding b j + r) := by
      calc
        _ = fun j => coordinateArmBase 1 j + r := hstep
        _ = fun j => grid.embedding b j + r := by simp [coordinateArmBase]
    exact structureMap_ne_zero_of_module_index_eq
      (M := finiteSimplicialHomology k boundaryTetrahedronGrading 1)
      (N := finiteSimplicialHomology k boundaryTetrahedronGrading 1) rfl hp hq
      (hne := homology_secondBirth_structureMap_ne_zero k r hr0 hr1)

/-- Each selected translated birth fiber is nonzero, witnessed by its surviving map. -/
theorem coordinateTranslatedHomology_birth_not_isZero (k : Type u) [Field k]
    (v : Fin 2 → ℝ) (i : Fin 2) :
    ¬ IsZero ((coordinateTranslatedHomology k v).obj (coordinateTranslatedBirth i v)) := by
  intro hz
  exact coordinateTranslatedHomology_birth_structureMap_ne_zero k v i 0
    (by norm_num) (by norm_num) (hz.eq_of_src _ _)

private theorem coordinateTranslated_map_zero_of_step (k : Type u) [Field k]
    (v : Fin 2 → ℝ) (p : Fin 2 → ℝ) {q : Fin 2 → ℝ} (hpq : p ≤ q)
    (hstep : ∀ i, q i = p i + 1) :
    structureMap (coordinateTranslatedHomology k v) hpq = 0 := by
  apply coordinateMap_zero_of_iso (coordinateTranslatedHomologyReindexIso k v) hpq
  rw [structureMap_reindex]
  have hz := translatedHomology_diagonal_one_zero k 0
    (coordinateTranslationPullback v p)
  have hq : coordinateTranslationPullback v q =
      fun i => coordinateTranslationPullback v p i + 1 := by
    funext i
    simp only [coordinateTranslationPullback_apply]
    rw [hstep]
    ring
  exact structureMap_zero_of_module_index_eq
    (M := finiteSimplicialHomology k boundaryTetrahedronGrading 1)
    (N := translatedHomology k 0) (translatedHomology_zero k).symm rfl hq
    (hz := hz)

/-- Every actual vector-translated module kills its one-unit diagonal transition. -/
theorem coordinateTranslatedHomology_diagonal_one_zero (k : Type u) [Field k]
    (v : Fin 2 → ℝ) (p : Fin 2 → ℝ) :
    structureMap (coordinateTranslatedHomology k v)
      (show p ≤ (fun i => p i + 1) from fun _ => le_add_of_nonneg_right (by norm_num)) = 0 :=
  coordinateTranslated_map_zero_of_step k v p
    (show p ≤ (fun i => p i + 1) from fun _ => le_add_of_nonneg_right (by norm_num))
    (fun _ => rfl)

/-- The maximum of the two actual signed coordinate errors, in NNReal. -/
def coordinateTranslationGap (u v : Fin 2 → ℝ) : ℝ≥0 :=
  max ‖v 0 - u 0‖₊ ‖v 1 - u 1‖₊

@[simp] theorem coordinateTranslationGap_coe (u v : Fin 2 → ℝ) :
    (coordinateTranslationGap u v : ℝ) =
      max |v 0 - u 0| |v 1 - u 1| := by
  simp [coordinateTranslationGap, Real.norm_eq_abs]

/-- Actual face-grade errors are bounded by the maximum coordinate displacement. -/
theorem coordinateTranslatedGrading_grade_error (u v : Fin 2 → ℝ)
    (σ : TotalFace boundaryTetrahedron.toPre) (i : Fin 2) :
    |(coordinateTranslatedGrading u).grade σ i -
      (coordinateTranslatedGrading v).grade σ i| ≤ (coordinateTranslationGap u v : ℝ) := by
  rw [coordinateTranslatedGrading_grade, coordinateTranslatedGrading_grade]
  have hdiff : (boundaryTetrahedronGrading.grade σ i + u i) -
      (boundaryTetrahedronGrading.grade σ i + v i) = u i - v i := by ring
  rw [hdiff, coordinateTranslationGap_coe]
  fin_cases i
  · rw [le_max_iff]
    exact Or.inl (le_of_eq (abs_sub_comm _ _))
  · rw [le_max_iff]
    exact Or.inr (le_of_eq (abs_sub_comm _ _))

/-- The grade-magnitude witness induced by actual simplicial sublevel inclusions. -/
noncomputable def coordinateTranslatedHomologyMagnitudeInterleaving
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    CoordinateInterleaving (coordinateTranslationGap u v)
      (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) :=
  finiteSimplicialHomology_interleaving k (coordinateTranslatedGrading u)
    (coordinateTranslatedGrading v) 1 (coordinateTranslatedGrading_grade_error u v)

@[simp] theorem coordinateTranslatedHomologyMagnitudeInterleaving_φ_app
    (k : Type u) [Field k] (u v p : Fin 2 → ℝ) :
    (coordinateTranslatedHomologyMagnitudeInterleaving k u v).φ.app p =
      simplicialHomologyIncl k
        ((coordinateTranslatedGrading u).sublevel_le_translation_of_error
          (coordinateTranslatedGrading v)
          (coordinateTranslatedGrading_grade_error u v) p) 1 :=
  finiteSimplicialHomology_interleaving_φ_app k _ _ 1 _ p

@[simp] theorem coordinateTranslatedHomologyMagnitudeInterleaving_ψ_app
    (k : Type u) [Field k] (u v p : Fin 2 → ℝ) :
    (coordinateTranslatedHomologyMagnitudeInterleaving k u v).ψ.app p =
      simplicialHomologyIncl k
        ((coordinateTranslatedGrading v).sublevel_le_translation_of_error
          (coordinateTranslatedGrading u) (fun σ i => by
            simpa only [abs_sub_comm] using coordinateTranslatedGrading_grade_error u v σ i) p) 1 :=
  finiteSimplicialHomology_interleaving_ψ_app k _ _ 1 _ p

/-- Zero cross maps interleave any pair of translates at half the unit lifetime. -/
noncomputable def coordinateTranslatedHomologyHalfInterleaving
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    CoordinateInterleaving (1 / 2) (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v) :=
  CoordinateInterleaving.ofStructureMapEquations 0 0
    (fun p => by
      change (0 : (coordinateTranslatedHomology k u).obj p ⟶
        (coordinateTranslatedHomology k v).obj (CoordinateShift.translation (1/2) p)) ≫ 0 = _
      rw [zero_comp]
      symm
      apply coordinateTranslated_map_zero_of_step k u p
      intro i
      simp only [CoordinateShift.translation_apply]
      norm_num
      ring)
    (fun p => by
      change (0 : (coordinateTranslatedHomology k v).obj p ⟶
        (coordinateTranslatedHomology k u).obj (CoordinateShift.translation (1/2) p)) ≫ 0 = _
      rw [zero_comp]
      symm
      apply coordinateTranslated_map_zero_of_step k v p
      intro i
      simp only [CoordinateShift.translation_apply]
      norm_num
      ring)

@[simp] theorem coordinateTranslatedHomologyHalfInterleaving_φ
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    (coordinateTranslatedHomologyHalfInterleaving k u v).φ = 0 := rfl

@[simp] theorem coordinateTranslatedHomologyHalfInterleaving_ψ
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    (coordinateTranslatedHomologyHalfInterleaving k u v).ψ = 0 := rfl

/-- An explicit optimal witness, using inclusions or the zero-map half witness. -/
noncomputable def coordinateTranslatedHomologyOptimalInterleaving
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    CoordinateInterleaving (min (coordinateTranslationGap u v) (1 / 2))
      (coordinateTranslatedHomology k u) (coordinateTranslatedHomology k v) := by
  by_cases h : coordinateTranslationGap u v ≤ (1 / 2 : ℝ≥0)
  · rw [min_eq_left h]
    exact coordinateTranslatedHomologyMagnitudeInterleaving k u v
  · rw [min_eq_right (le_of_not_ge h)]
    exact coordinateTranslatedHomologyHalfInterleaving k u v

private theorem coordinateTranslatedBirth_map_ne_zero_of_step (k : Type u) [Field k]
    (v : Fin 2 → ℝ) (i : Fin 2) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {q : Fin 2 → ℝ} (hbq : coordinateTranslatedBirth i v ≤ q)
    (hstep : ∀ j, q j = coordinateTranslatedBirth i v j + r) :
    structureMap (coordinateTranslatedHomology k v) hbq ≠ 0 := by
  have hq : q = fun j => coordinateTranslatedBirth i v j + r := funext hstep
  subst q
  exact coordinateTranslatedHomology_birth_structureMap_ne_zero k v i r hr0 hr1

private theorem coordinateTranslatedHomology_no_interleaving_of_positive_gap
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) (i : Fin 2) (ε : ℝ≥0)
    (hgap : (ε : ℝ) < v i - u i) (hlife : 2 * (ε : ℝ) < 1) :
    IsEmpty (CoordinateInterleaving ε (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v)) := by
  refine ⟨fun I => ?_⟩
  let p := coordinateTranslatedBirth i u
  have hzero : IsZero ((coordinateTranslatedHomology k v).obj
      (CoordinateShift.translation ε p)) := by
    apply coordinateTranslatedHomology_isZero_of_coordinate_lt k v i
    simp only [CoordinateShift.translation_apply, p, coordinateTranslatedBirth_selected]
    linarith
  have hf : I.φ.app p = 0 := hzero.eq_of_tgt _ _
  have hsurvive : structureMap (coordinateTranslatedHomology k u)
      (CoordinateInterleaving.twice_le ε p) ≠ 0 := by
    apply coordinateTranslatedBirth_map_ne_zero_of_step k u i (2 * (ε : ℝ))
      (by positivity) hlife
    intro j
    simp only [CoordinateShift.translation_apply]
    ring
  exact hsurvive (by erw [← I.φ_ψ_structureMap p, hf, zero_comp])

/-- A gap in either selected coordinate obstructs any radius below it and half-lifetime. -/
theorem coordinateTranslatedHomology_no_interleaving (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) (i : Fin 2) (ε : ℝ≥0)
    (hgap : (ε : ℝ) < |v i - u i|) (hlife : 2 * (ε : ℝ) < 1) :
    IsEmpty (CoordinateInterleaving ε (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v)) := by
  by_cases hsign : v i - u i ≥ 0
  · have hpos : (ε : ℝ) < v i - u i := by
      rwa [abs_of_nonneg hsign] at hgap
    exact coordinateTranslatedHomology_no_interleaving_of_positive_gap
      k u v i ε hpos hlife
  · have hneg : (ε : ℝ) < u i - v i := by
      rw [abs_of_neg (lt_of_not_ge hsign)] at hgap
      linarith
    refine ⟨fun hI => ?_⟩
    exact (coordinateTranslatedHomology_no_interleaving_of_positive_gap
      k v u i ε hneg hlife).false hI.symm

private theorem coordinateOptimalRadius_coe (u v : Fin 2 → ℝ) :
    ((min (coordinateTranslationGap u v) (1 / 2 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) := by
  rw [ENNReal.coe_nnreal_eq]
  simp [coordinateTranslationGap_coe]

private theorem coordinateDistance_lower (k : Type u) [Field k]
    (u v : Fin 2 → ℝ) :
    ENNReal.ofReal (min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) ≤
      coordinateInterleavingDistance (coordinateTranslatedHomology k u)
        (coordinateTranslatedHomology k v) := by
  apply le_coordinateInterleavingDistance_iff.mpr
  rintro ε ⟨I⟩
  have hr : min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2 : ℝ) ≤ (ε : ℝ) := by
    by_contra h
    have hlt : (ε : ℝ) < min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2 : ℝ) :=
      lt_of_not_ge h
    have hgap : (ε : ℝ) < max |v 0 - u 0| |v 1 - u 1| :=
      hlt.trans_le (min_le_left _ _)
    have hlife : 2 * (ε : ℝ) < 1 := by
      have hhalf := hlt.trans_le (min_le_right _ _)
      linarith
    rcases (lt_max_iff).mp hgap with hfirst | hsecond
    · have h := coordinateTranslatedHomology_no_interleaving k u v 0 ε hfirst hlife
      exact h.false I
    · have h := coordinateTranslatedHomology_no_interleaving k u v 1 ε hsecond hlife
      exact h.false I
  simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr

/-- Exact extended distance for every signed independent coordinate translation. -/
theorem coordinateInterleavingDistance_coordinateTranslatedHomology
    (k : Type u) [Field k] (u v : Fin 2 → ℝ) :
    coordinateInterleavingDistance (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v) =
        ENNReal.ofReal (min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) := by
  have upper : coordinateInterleavingDistance (coordinateTranslatedHomology k u)
      (coordinateTranslatedHomology k v) ≤
        ENNReal.ofReal (min (max |v 0 - u 0| |v 1 - u 1|) (1 / 2)) := by
    simpa only [coordinateOptimalRadius_coe] using
      (coordinateTranslatedHomologyOptimalInterleaving k u v).distance_le
  exact le_antisymm upper (coordinateDistance_lower k u v)

/-- On the diagonal, the independent-translation formula invokes the scalar theorem. -/
theorem coordinateInterleavingDistance_const_translatedHomology (k : Type u) [Field k]
    (s t : ℝ) :
    coordinateInterleavingDistance (coordinateTranslatedHomology k (fun _ => s))
      (coordinateTranslatedHomology k (fun _ => t)) =
        ENNReal.ofReal (min |t - s| (1 / 2)) := by
  rw [coordinateInterleavingDistance_congr
    (eqToIso (coordinateTranslatedHomology_const k s))
    (eqToIso (coordinateTranslatedHomology_const k t))]
  exact coordinateInterleavingDistance_translatedHomology k s t

end TDA.Persistence.RankResolutionDegreeTwoSimplicial
