import TDA.Persistence.Reduction.FiniteInputVertexMap

/-! Compare the finite chain-image matrix with the existing signed vertex-chain map. -/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace TDA.Persistence.Reduction.FiniteInput

open TDA.Simplicial TDA.Filtration

/-- The original list position of an actual sublevel face. -/
noncomputable def sublevelFaceIndex (xs : Input) (h : Valid xs) {p : ℕ} {a : ℤ}
    (s : Face ((gradeFilter xs h).sublevel a) p) : Fin xs.length :=
  (listEquiv xs h).symm ⟨s.1, Classical.choose s.2.1⟩

theorem sublevelFaceIndex_face (xs : Input) (h : Valid xs) {p : ℕ} {a : ℤ}
    (s : Face ((gradeFilter xs h).sublevel a) p) :
    (xs.get (sublevelFaceIndex xs h s)).1 = s.1 :=
  congrArg Subtype.val ((listEquiv xs h).apply_symm_apply _)

theorem sublevelFaceIndex_grade (xs : Input) (h : Valid xs) {p : ℕ} {a : ℤ}
    (s : Face ((gradeFilter xs h).sublevel a) p) :
    (xs.get (sublevelFaceIndex xs h s)).2 ≤ a :=
  Classical.choose_spec s.2.1

theorem sublevelFaceIndex_degree (xs : Input) (h : Valid xs) {p : ℕ} {a : ℤ}
    (s : Face ((gradeFilter xs h).sublevel a) p) :
    degree xs (sublevelFaceIndex xs h s) = p := by
  unfold degree
  rw [sublevelFaceIndex_face, s.2.2]
  omega

/-- Read an actual sublevel chain in its original list-face coordinates. -/
noncomputable def sublevelChainVector (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    Chain ((gradeFilter xs h).sublevel a) (ZMod 2) p →ₗ[ZMod 2]
      (Fin xs.length → ZMod 2) := by
  let := faceFintype xs h
  exact
    { toFun := fun c i =>
        (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) p
          (chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p c)).1
            ((finCongr (faceCount_eq_length xs h)).symm i)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

theorem sublevelChainVector_cycle (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    sublevelChainVector xs h p a (vectorSublevelCycle xs h p a v hv).1 = v := by
  let := faceFintype xs h
  funext i
  have hc := congrFun (vectorSublevelCycle_coordinates xs h p a v hv)
    ((finCongr (faceCount_eq_length xs h)).symm i)
  simpa only [sublevelChainVector, LinearMap.coe_mk, AddHom.coe_mk, faceVector, simplicialCycleIncl_coe,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self] using hc

theorem faceVector_sublevelChainVector (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (c : Chain ((gradeFilter xs h).sublevel a) (ZMod 2) p) :
    letI := faceFintype xs h
    faceVector xs h (sublevelChainVector xs h p a c) =
      (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) p
        (chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p c)).1 := by
  let := faceFintype xs h
  funext i
  simp only [faceVector, sublevelChainVector, LinearMap.coe_mk, AddHom.coe_mk,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]

theorem sublevelChainVector_injective (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ) :
    Function.Injective (sublevelChainVector xs h p a) := by
  let := faceFintype xs h
  intro c d hcd
  have hp : chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p c =
      chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p d := by
    apply (prefixChainEquiv (ZMod 2) (compatibleOrder xs h) (sublevelStage xs a) p).injective
    apply Subtype.ext
    rw [← faceVector_sublevelChainVector, ← faceVector_sublevelChainVector, hcd]
  have he := congrArg (chainIncl (ZMod 2) (sublevel_eq_prefix xs h a).ge p) hp
  simpa only [← LinearMap.comp_apply, ← chainIncl_comp, chainIncl_id, LinearMap.id_apply] using he

/-- Every actual signed cycle passes the finite original-face cycle conditions. -/
theorem sublevelChainVector_cycleInput (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (z : simplicialCycles ((gradeFilter xs h).sublevel a) (ZMod 2) p) :
    CycleInput xs p a (sublevelChainVector xs h p a z.1) := by
  let := faceFintype xs h
  let E := finCongr (faceCount_eq_length xs h)
  let zp := simplicialCycleIncl (ZMod 2) (sublevel_eq_prefix xs h a).le p z
  have hz := (prefixChainEquiv_cycle_iff (ZMod 2) (compatibleOrder xs h)
    (sublevelStage xs a) p zp.1).mp zp.2
  apply (cycleInput_iff_originalCycle xs h p a _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact hz.1 (E.symm i) hi
  · intro i hi
    exact hz.2.1 (E.symm i) (by rwa [← degree_eq_faceDegree xs h i])
  · have hb : faceVector xs h ((boundary xs).mulVec (sublevelChainVector xs h p a z.1)) = 0 := by
      rw [boundary_faceVector, faceVector_sublevelChainVector]
      simpa only [zp, simplicialCycleIncl_coe] using hz.2.2
    funext i
    have he := congrFun hb (E.symm i)
    simpa only [faceVector, E, finCongr_symm, finCongr_apply, Fin.cast_cast,
      Fin.cast_eq_self, Pi.zero_apply] using he

private theorem prefixFaceIndex_cast (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (s : Face ((gradeFilter xs h).sublevel a) p) :
    let := faceFintype xs h
    Fin.cast (faceCount_eq_length xs h)
      (prefixFaceIndex (compatibleOrder xs h) (sublevelStage xs a) p
        (faceIncl (sublevel_eq_prefix xs h a).le p s)).1 = sublevelFaceIndex xs h s := by
  let := faceFintype xs h
  apply (listEquiv xs h).injective
  apply Subtype.ext
  change (xs.get _).1 = (xs.get (sublevelFaceIndex xs h s)).1
  rw [sublevelFaceIndex_face]
  rw [← positionEquiv_val]
  change ((positionEquiv xs h) ((positionEquiv xs h).symm ⟨s.1, _⟩)).1 = s.1
  exact congrArg Subtype.val ((positionEquiv xs h).apply_symm_apply _)

/-- An actual simplex has exactly its original list coefficient. -/
theorem sublevelChainVector_single (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (s : Face ((gradeFilter xs h).sublevel a) p) (z : ZMod 2) :
    sublevelChainVector xs h p a (Finsupp.single s z) =
      Pi.single (sublevelFaceIndex xs h s) z := by
  let := faceFintype xs h
  funext i
  dsimp only [sublevelChainVector, LinearMap.coe_mk, AddHom.coe_mk]
  rw [chainIncl_single, prefixChainEquiv_single_apply]
  have he : ((finCongr (faceCount_eq_length xs h)).symm i =
      (prefixFaceIndex (compatibleOrder xs h) (sublevelStage xs a) p
        (faceIncl (sublevel_eq_prefix xs h a).le p s)).1) ↔
      i = sublevelFaceIndex xs h s := by
    rw [← prefixFaceIndex_cast xs h p a s]
    constructor
    · intro hi
      exact congrArg (finCongr (faceCount_eq_length xs h)) hi
    · intro hi
      simpa only [finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self] using
        congrArg (finCongr (faceCount_eq_length xs h)).symm hi
  simp only [he, Pi.single_apply]

private theorem image_card_eq_iff (s : Finset ℕ) {n : ℕ} (hn : s.card = n) (f : ℕ → ℕ) :
    (s.image f).card = s.card ↔ Function.Injective (f ∘ s.orderEmbOfFin hn) := by
  rw [Finset.card_image_iff]
  constructor
  · intro h i j hij
    exact (s.orderEmbOfFin hn).injective
      (h (s.orderEmbOfFin_mem hn i) (s.orderEmbOfFin_mem hn j) hij)
  · intro h x hx y hy hxy
    have hx' : x ∈ Set.range (s.orderEmbOfFin hn) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    have hy' : y ∈ Set.range (s.orderEmbOfFin hn) := by
      rw [Finset.range_orderEmbOfFin]
      exact hy
    obtain ⟨i, rfl⟩ := hx'
    obtain ⟨j, rfl⟩ := hy'
    exact congrArg (s.orderEmbOfFin hn) (h hxy)

private theorem vertexImageFace_val {K L : PreAbstractSimplicialComplex ℕ}
    (f : VertexMap K L) (p : ℕ) (s : Face K p)
    (hi : Function.Injective (f ∘ s.1.orderEmbOfFin s.2.2)) :
    (vertexImageFace f s hi).1 = s.1.image f := by
  change Finset.univ.image (f ∘ s.1.orderEmbOfFin s.2.2) = s.1.image f
  rw [← Finset.image_image, Finset.image_orderEmbOfFin_univ]

private theorem vertexChainMap_f2_single {K L : PreAbstractSimplicialComplex ℕ}
    (f : VertexMap K L) (p : ℕ) (s : Face K p) (z : ZMod 2)
    (hi : Function.Injective (f ∘ s.1.orderEmbOfFin s.2.2)) :
    vertexChainMap (ZMod 2) f p (Finsupp.single s z) =
      Finsupp.single (vertexImageFace f s hi) z := by
  rw [vertexChainMap_single_of_injective (ZMod 2) f p s z hi]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort (f ∘ s.1.orderEmbOfFin s.2.2))) with hs | hs
  · simp [hs]
  · simp only [hs, Units.val_neg, Units.val_one, neg_one_zsmul,
      Finsupp.smul_single, smul_eq_mul]
    simp only [show (-1 : ZMod 2) = 1 from by decide, mul_one]

private theorem face_eq_iff_index (xs : Input) (h : Valid xs) (p : ℕ) (a : ℤ)
    (s : Face ((gradeFilter xs h).sublevel a) p) (i : Fin xs.length) :
    (xs.get i).1 = s.1 ↔ i = sublevelFaceIndex xs h s := by
  constructor
  · intro hi
    apply (listFace_bijective xs h).1
    apply Subtype.ext
    exact hi.trans (sublevelFaceIndex_face xs h s).symm
  · rintro rfl
    exact sublevelFaceIndex_face xs h s

private theorem chainImage_single (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (s : Face ((gradeFilter xs hx).sublevel a) p) (z : ZMod 2) :
    sublevelChainVector ys hy p b
        (vertexChainMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p (Finsupp.single s z)) =
      (vertexMatrix xs ys a f).mulVec
        (sublevelChainVector xs hx p a (Finsupp.single s z)) := by
  rw [sublevelChainVector_single, Matrix.mulVec_single]
  change _ = fun i => vertexMatrix xs ys a f i (sublevelFaceIndex xs hx s) * z
  let F := validatedVertexMap xs ys hx hy a b f hm
  have hface := sublevelFaceIndex_face xs hx s
  have hgrade := sublevelFaceIndex_grade xs hx s
  by_cases hi : Function.Injective (f ∘ s.1.orderEmbOfFin s.2.2)
  · have hc := (image_card_eq_iff s.1 s.2.2 f).mpr hi
    rw [vertexChainMap_f2_single F p s z hi, sublevelChainVector_single]
    have ht := vertexImageFace_val F p s hi
    funext i
    have he := face_eq_iff_index ys hy p b (vertexImageFace F s hi) i
    rw [ht] at he
    change (ys.get i).1 = s.1.image f ↔ i = sublevelFaceIndex ys hy (vertexImageFace F s hi) at he
    simp only [vertexMatrix, hface, hgrade, hc, true_and, he, Pi.single_apply,
      ite_mul, one_mul, zero_mul]
  · have hc : (s.1.image f).card ≠ s.1.card :=
      fun h => hi ((image_card_eq_iff s.1 s.2.2 f).mp h)
    rw [vertexChainMap_single_of_not_injective (ZMod 2) F p s z hi, map_zero]
    funext i
    simp only [vertexMatrix, hface, hc, and_false, false_and, ite_false, zero_mul, Pi.zero_apply]

/-- The executed rectangular matrix is the actual signed chain map over F₂. -/
theorem sublevelChainVector_vertexChainMap (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (c : Chain ((gradeFilter xs hx).sublevel a) (ZMod 2) p) :
    sublevelChainVector ys hy p b
        (vertexChainMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p c) =
      vertexVector xs ys a f (sublevelChainVector xs hx p a c) := by
  have he : (sublevelChainVector ys hy p b).comp
      (vertexChainMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p) =
      (vertexMatrix xs ys a f).mulVecLin.comp (sublevelChainVector xs hx p a) := by
    apply Finsupp.lhom_ext
    intro s z
    exact chainImage_single xs ys hx hy p a b f hm s z
  exact LinearMap.congr_fun he c

private theorem vertexChainMap_mem_cycles {K L : PreAbstractSimplicialComplex ℕ}
    (f : VertexMap K L) (p : ℕ) (z : simplicialCycles K (ZMod 2) p) :
    vertexChainMap (ZMod 2) f p z.1 ∈ simplicialCycles L (ZMod 2) p := by
  cases p with
  | zero => rw [simplicialCycles_zero]; trivial
  | succ q =>
    rw [simplicialCycles_succ, LinearMap.mem_ker]
    have hz : TDA.Simplicial.boundary K (ZMod 2) q z.1 = 0 := by
      simpa only [simplicialCycles_succ, LinearMap.mem_ker] using z.2
    have he := LinearMap.congr_fun (boundary_vertexChainMap (ZMod 2) f q) z.1
    simpa only [LinearMap.comp_apply, hz, map_zero] using he

/-- The computed image of an admitted cycle is an admitted target cycle. -/
theorem vertexVector_cycleInput (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    CycleInput ys p b (vertexVector xs ys a f v) := by
  let z := vectorSublevelCycle xs hx p a v hv
  let F := validatedVertexMap xs ys hx hy a b f hm
  have he := sublevelChainVector_cycleInput ys hy p b
    ⟨vertexChainMap (ZMod 2) F p z.1, vertexChainMap_mem_cycles F p z⟩
  rw [sublevelChainVector_vertexChainMap, sublevelChainVector_cycle] at he
  exact he

/-- The supplied cycle's computed image represents its pre-existing induced homology image. -/
theorem vertexVector_class (xs ys : Input) (hx : Valid xs) (hy : Valid ys)
    (p : ℕ) (a b : ℤ) (f : ℕ → ℕ) (hm : VertexMapCondition xs ys a b f)
    (v : Fin xs.length → ZMod 2) (hv : CycleInput xs p a v) :
    (simplicialHomologyMap (ZMod 2) (validatedVertexMap xs ys hx hy a b f hm) p).hom
        (vectorSublevelClass xs hx p a v hv) =
      vectorSublevelClass ys hy p b (vertexVector xs ys a f v)
        (vertexVector_cycleInput xs ys hx hy p a b f hm v hv) := by
  apply simplicialHomologyMap_class
  apply sublevelChainVector_injective ys hy p b
  rw [sublevelChainVector_vertexChainMap, sublevelChainVector_cycle, sublevelChainVector_cycle]

end TDA.Persistence.Reduction.FiniteInput
