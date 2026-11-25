import TDA.Sheaf.AlternatingReflection

/-!
# Reflection at a source and the splitting of singleton summands

Let `p` be a source of `o` and let `o'` reverse the arrows at `p`. The source reflection replaces
the space at `p` by the cokernel of the signed map `v ↦ (± M(p → l) v)_l` into the outgoing
neighbours (the pushout at an interior vertex) and makes `p` a sink. As for the sink
reflection, every space is a quotient of the product of all vertex spaces, so no space is
transported between vertices. Only the diagram is constructed here.

When the outgoing maps at `p` are jointly injective, reflecting back at the sink `p` recovers
the diagram: `reflectSourceUnitIso`. Otherwise a vector in their common kernel spans a direct
summand isomorphic to the singleton interval `{p}`: `isoSingletonBiprod`.
-/

universe u

namespace TDA.Sheaf.AlternatingDiagram

open CategoryTheory Limits TDA.Persistence
open ZeroObject

variable {n : ℕ} {k : Type u} [Field k] {o o' : Fin n → Bool} {p : Fin (n + 1)}

/-- The coordinates killed in the quotient at `j`: the out-neighbours of `p` at `p`, and `j`
itself elsewhere. -/
def srcSupp (o : Fin n → Bool) (p j l : Fin (n + 1)) : Prop :=
  if j = p then Arrow o p l else l = j

instance srcSuppDecidable (o : Fin n → Bool) (p j l : Fin (n + 1)) :
    Decidable (srcSupp o p j l) := by
  unfold srcSupp; infer_instance

/-- The signed map from `p` to its outgoing neighbours, into the product of all spaces. -/
noncomputable def srcDelta (M : Diagram k o) (p : Fin (n + 1)) :
    M.obj (vtx o p) →ₗ[k] Tot M :=
  LinearMap.pi (fun l => sgn (k := k) p l • arr M p l)

@[simp]
theorem srcDelta_apply (M : Diagram k o) (p : Fin (n + 1)) (v : M.obj (vtx o p))
    (l : Fin (n + 1)) : srcDelta M p v l = sgn (k := k) p l • arr M p l v := rfl

/-- The relations of the reflected space at `j`. -/
noncomputable def srcRel (M : Diagram k o) (p j : Fin (n + 1)) : Submodule k (Tot M) :=
  (⨅ l, ⨅ (_ : srcSupp o p j l), LinearMap.ker (pr M l)) ⊔
    (if j = p then LinearMap.range (srcDelta M p) else ⊥)

theorem mem_srcRel_of_ne (M : Diagram k o) {p j : Fin (n + 1)} (hj : j ≠ p) (x : Tot M) :
    x ∈ srcRel M p j ↔ x j = 0 := by
  unfold srcRel
  simp only [hj, ite_false, sup_bot_eq, Submodule.mem_iInf, LinearMap.mem_ker, srcSupp]
  constructor
  · intro h; exact h j rfl
  · intro h l hl; subst hl; exact h

theorem mem_srcRel_self (M : Diagram k o) (p : Fin (n + 1)) (x : Tot M) :
    x ∈ srcRel M p p ↔ ∃ v, ∀ l, Arrow o p l → x l = srcDelta M p v l := by
  unfold srcRel
  simp only [ite_true, srcSupp]
  constructor
  · intro h
    obtain ⟨a, ha, b, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.mp h
    refine ⟨v, fun l hl => ?_⟩
    have : a l = 0 := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at ha
      exact ha l hl
    simp [this]
  · rintro ⟨v, hv⟩
    refine Submodule.mem_sup.mpr ⟨x - srcDelta M p v, ?_, srcDelta M p v, ⟨v, rfl⟩, by simp⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro l hl
    simp [hv l hl]

/-- The reflected space at `j`. -/
abbrev srcSpace (M : Diagram k o) (p j : Fin (n + 1)) := Tot M ⧸ srcRel M p j

/-- The map of the source reflection along an arrow from `i` to `j`. -/
noncomputable def srcLift (M : Diagram k o) (p i j : Fin (n + 1)) : Tot M →ₗ[k] Tot M := by
  classical
  exact if j = p then ins M i ∘ₗ pr M i else ins M j ∘ₗ arr M i j ∘ₗ pr M i

theorem srcLift_apply_self (M : Diagram k o) {p j : Fin (n + 1)} (hj : j = p) (i : Fin (n + 1))
    (x : Tot M) : srcLift M p i j x = Pi.single i (x i) := by
  simp [srcLift, hj]

theorem srcLift_apply_of_ne (M : Diagram k o) {p j : Fin (n + 1)} (hj : j ≠ p) (i : Fin (n + 1))
    (x : Tot M) : srcLift M p i j x = Pi.single j (arr M i j (x i)) := by
  simp [srcLift, hj]

theorem srcLift_le (M : Diagram k o) (hs : IsSource o p) (hf : IsFlipAt o o' p)
    {i j : Fin (n + 1)} (h : Arrow o' i j) :
    srcRel M p i ≤ (srcRel M p j).comap (srcLift M p i j) := by
  have hi : i ≠ p := by
    rintro rfl
    exact hf.isSink hs j h
  intro x hx
  rw [mem_srcRel_of_ne M hi] at hx
  rw [Submodule.mem_comap]
  have : srcLift M p i j x = 0 := by
    by_cases hj : j = p
    · rw [srcLift_apply_self M hj, hx, Pi.single_zero]
    · rw [srcLift_apply_of_ne M hj, hx, map_zero, Pi.single_zero]
  rw [this]
  exact Submodule.zero_mem _

variable (o')

/-- The reflection of a diagram at a source `p`, on the orientation `o'` that reverses the
arrows at `p`. -/
noncomputable def reflectSource (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o) :
    Diagram k o' :=
  ofArrows (fun j => ModuleCat.of k (srcSpace M p j))
    (fun {i j} h => ModuleCat.ofHom (Submodule.mapQ _ _ (srcLift M p i j) (srcLift_le M hs hf h)))

variable {o'}

instance reflectSource_finiteDimensional (hs : IsSource o p) (hf : IsFlipAt o o' p)
    (M : Diagram k o) [∀ X, FiniteDimensional k (M.obj X)] (X : Paths (Vertex o')) :
    FiniteDimensional k ((reflectSource o' hs hf M).obj X) := by
  change FiniteDimensional k (srcSpace M p X)
  infer_instance

/-- The quotient map onto the reflected space at `j`. -/
noncomputable def qmk (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) : Tot M →ₗ[k] (reflectSource o' hs hf M).obj (vtx o' j) :=
  (srcRel M p j).mkQ

theorem qmk_surjective (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) : Function.Surjective (qmk hs hf M j) :=
  Submodule.mkQ_surjective _

theorem qmk_eq_zero_iff (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) (x : Tot M) : qmk hs hf M j x = 0 ↔ x ∈ srcRel M p j :=
  Submodule.Quotient.mk_eq_zero _

theorem qmk_eq_iff (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) (x y : Tot M) : qmk hs hf M j x = qmk hs hf M j y ↔ x - y ∈ srcRel M p j :=
  Submodule.Quotient.eq _

theorem reflectSource_map_gen (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    {i j : Fin (n + 1)} (h : Arrow o' i j) (x : Tot M) :
    ((reflectSource o' hs hf M).map (gen h)).hom (qmk hs hf M i x) =
      qmk hs hf M j (srcLift M p i j x) := by
  simp only [reflectSource, ofArrows_map_gen]
  rfl

theorem arr_reflectSource_qmk (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (i j : Fin (n + 1)) (x : Tot M) :
    arr (reflectSource o' hs hf M) i j (qmk hs hf M i x) =
      if Arrow o' i j then qmk hs hf M j (srcLift M p i j x) else 0 := by
  by_cases h : Arrow o' i j
  · rw [arr_of_arrow _ h, reflectSource_map_gen, if_pos h]
  · rw [arr_of_not_arrow _ h, if_neg h]; rfl

/-! ### Reflecting back: the unit -/

/-- The outgoing maps at `p` are jointly injective. -/
def OutInjective (M : Diagram k o) (p : Fin (n + 1)) : Prop :=
  ∀ v : M.obj (vtx o p), (∀ l, arr M p l v = 0) → v = 0

/-- The comparison from a diagram to the sink reflection of its source reflection, into the
product of the vertex spaces. -/
noncomputable def unitMap (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) : M.obj (vtx o j) →ₗ[k] Tot (reflectSource o' hs hf M) := by
  classical
  exact LinearMap.pi (fun l => if sinkSupp o' p j l then
    qmk hs hf M l ∘ₗ (if j = p then ins M l ∘ₗ arr M j l else ins M j) else 0)

theorem unitMap_apply (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) (v : M.obj (vtx o j)) (l : Fin (n + 1)) :
    unitMap hs hf M j v l = if sinkSupp o' p j l then
      qmk hs hf M l (if j = p then Pi.single l (arr M j l v) else Pi.single j v) else 0 := by
  unfold unitMap
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

theorem unitMap_mem (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) (v : M.obj (vtx o j)) :
    unitMap hs hf M j v ∈ sinkSpace (reflectSource o' hs hf M) p j := by
  rw [mem_sinkSpace]
  refine ⟨fun l hl => by rw [unitMap_apply, if_neg hl], fun hj => ?_⟩
  subst hj
  rw [sinkSum_apply]
  have hterm : ∀ l, sgn (k := k) j l • arr (reflectSource o' hs hf M) l j (unitMap hs hf M j v l) =
      qmk hs hf M j (if Arrow o' l j then sgn (k := k) j l • Pi.single l (arr M j l v)
        else 0) := by
    intro l
    rw [unitMap_apply]
    by_cases hl : Arrow o' l j
    · have hs' : sinkSupp o' j j l := by simp [sinkSupp, hl]
      rw [if_pos hs', if_pos rfl, arr_reflectSource_qmk, if_pos hl, if_pos hl,
        srcLift_apply_self M rfl, map_smul, Pi.single_eq_same]
    · have hs' : ¬ sinkSupp o' j j l := by simp [sinkSupp, hl]
      rw [if_neg hs', if_neg hl, map_zero, map_zero, smul_zero]
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← map_sum, qmk_eq_zero_iff, mem_srcRel_self]
  refine ⟨v, fun l hl => ?_⟩
  have hl' : Arrow o' l j := by
    rw [hf l j]; simp [hl]
  rw [Finset.sum_apply, Finset.sum_eq_single l]
  · simp [hl']
  · intro m _ hm
    split_ifs <;> simp [Ne.symm hm]
  · simp

theorem qmk_single_self (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    {j : Fin (n + 1)} (hj : j ≠ p) (w : Tot M) :
    qmk hs hf M j (Pi.single j (w j)) = qmk hs hf M j w := by
  rw [qmk_eq_iff, mem_srcRel_of_ne M hj]
  simp

theorem unitMap_apply_of_ne (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    {j : Fin (n + 1)} (hj : j ≠ p) (v : M.obj (vtx o j)) (l : Fin (n + 1)) :
    unitMap hs hf M j v l = if l = j then qmk hs hf M l (Pi.single j v) else 0 := by
  rw [unitMap_apply]
  simp only [sinkSupp, hj, ite_false]

theorem unitMap_injective (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (hinj : OutInjective M p) (j : Fin (n + 1)) : Function.Injective (unitMap hs hf M j) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  by_cases hj : j = p
  · subst hj
    apply hinj
    intro l
    by_cases hl : Arrow o j l
    · have hl' : Arrow o' l j := by rw [hf l j]; simp [hl]
      have hl0 : l ≠ j := hl.ne.symm
      have := congrFun hv l
      rw [unitMap_apply, if_pos (by simp [sinkSupp, hl']), if_pos rfl] at this
      have h2 := (qmk_eq_zero_iff hs hf M l _).mp this
      rw [mem_srcRel_of_ne M hl0] at h2
      simpa using h2
    · exact arr_of_not_arrow M hl ▸ rfl
  · have := congrFun hv j
    rw [unitMap_apply_of_ne hs hf M hj, if_pos rfl] at this
    have h2 := (qmk_eq_zero_iff hs hf M j _).mp this
    rw [mem_srcRel_of_ne M hj] at h2
    simpa using h2

theorem unitMap_surjective (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) (y : Tot (reflectSource o' hs hf M))
    (hy : y ∈ sinkSpace (reflectSource o' hs hf M) p j) : ∃ v, unitMap hs hf M j v = y := by
  rw [mem_sinkSpace] at hy
  obtain ⟨hsupp, hsum⟩ := hy
  choose w hw using fun l => qmk_surjective hs hf M l (y l)
  by_cases hj : j = p
  · subst hj
    have hsum' := hsum rfl
    rw [sinkSum_apply] at hsum'
    have hterm : ∀ l, sgn (k := k) j l • arr (reflectSource o' hs hf M) l j (y l) =
        qmk hs hf M j (if Arrow o' l j then sgn (k := k) j l • Pi.single l (w l l) else 0) := by
      intro l
      rw [← hw l, arr_reflectSource_qmk]
      by_cases hl : Arrow o' l j
      · rw [if_pos hl, if_pos hl, srcLift_apply_self M rfl, map_smul]
      · rw [if_neg hl, if_neg hl, map_zero, smul_zero]
    rw [Finset.sum_congr rfl (fun l _ => hterm l), ← map_sum, qmk_eq_zero_iff,
      mem_srcRel_self] at hsum'
    obtain ⟨v, hv⟩ := hsum'
    refine ⟨v, funext fun l => ?_⟩
    rw [unitMap_apply, if_pos rfl]
    by_cases hl : Arrow o' l j
    · have hl' : Arrow o j l := by
        have := (hf l j).mp hl; simpa using this
      have hl0 : l ≠ j := hl'.ne.symm
      have hvl := hv l hl'
      rw [Finset.sum_apply, Finset.sum_eq_single l (fun m _ hm => by
        split_ifs <;> simp [Ne.symm hm]) (by simp)] at hvl
      simp only [if_pos hl, Pi.smul_apply, Pi.single_eq_same, srcDelta_apply] at hvl
      have hval : w l l = arr M j l v := smul_right_injective _ (sgn_ne_zero j l) hvl
      rw [if_pos (by simp [sinkSupp, hl]), ← hval, qmk_single_self hs hf M hl0, hw]
    · rw [if_neg (by simp [sinkSupp, hl]), hsupp l (by simp [sinkSupp, hl])]
  · refine ⟨w j j, funext fun l => ?_⟩
    rw [unitMap_apply_of_ne hs hf M hj]
    by_cases hl : l = j
    · subst hl
      rw [if_pos rfl, qmk_single_self hs hf M hj, hw]
    · rw [if_neg hl, hsupp l (by simp [sinkSupp, hj, hl])]

/-- The unit as a map into the reflected space. -/
noncomputable def unitComp (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) : M.obj (vtx o j) →ₗ[k] sinkSpace (reflectSource o' hs hf M) p j :=
  (unitMap hs hf M j).codRestrict _ (unitMap_mem hs hf M j)

theorem unitComp_bijective (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (hinj : OutInjective M p) (j : Fin (n + 1)) : Function.Bijective (unitComp hs hf M j) := by
  constructor
  · intro v w h
    exact unitMap_injective hs hf M hinj j (congrArg Subtype.val h)
  · rintro ⟨y, hy⟩
    obtain ⟨v, hv⟩ := unitMap_surjective hs hf M j y hy
    exact ⟨v, Subtype.ext hv⟩

theorem unitMap_naturality (hs : IsSource o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    {i j : Fin (n + 1)} (h : Arrow o i j) (v : M.obj (vtx o i)) :
    unitMap hs hf M j ((M.map (gen h)).hom v) =
      sinkLift (reflectSource o' hs hf M) p i j (unitMap hs hf M i v) := by
  have hj : j ≠ p := by rintro rfl; exact hs i h
  rw [← arr_of_arrow M h]
  funext l
  rw [unitMap_apply_of_ne hs hf M hj]
  by_cases hip : i = p
  · subst hip
    rw [sinkLift_apply_self _ rfl]
    have hji : Arrow o' j i := by rw [hf j i]; simp [h]
    have hsupp : sinkSupp o' i i j := by simp [sinkSupp, hji]
    rw [unitMap_apply hs hf M i v j, if_pos hsupp, if_pos (rfl : i = i)]
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl]
  · rw [sinkLift_apply_of_ne _ hip, unitMap_apply_of_ne hs hf M hip, if_pos rfl,
      arr_reflectSource_qmk]
    have hij : Arrow o' i j := by
      rw [hf i j, if_neg (by rintro (h' | h') <;> contradiction)]; exact h
    rw [if_pos hij, srcLift_apply_of_ne M hj, Pi.single_eq_same]
    by_cases hl : l = j
    · subst hl; simp
    · simp [hl]

/-- A diagram whose outgoing maps at the source `p` are jointly injective is recovered by
reflecting at `p` and then back. -/
noncomputable def reflectSourceUnitIso (hs : IsSource o p) (hf : IsFlipAt o o' p)
    (M : Diagram k o) (hinj : OutInjective M p) :
    M ≅ (reflectSink o (hf.isSink hs) hf.symm).obj (reflectSource o' hs hf M) :=
  isoMk (fun X => (LinearEquiv.ofBijective (unitComp hs hf M X)
    (unitComp_bijective hs hf M hinj X)).toModuleIso) (fun {i j} h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change unitMap hs hf M j ((M.map (gen h)).hom v) = _
      rw [unitMap_naturality hs hf M h v]
      rw [ModuleCat.comp_apply]
      erw [reflectSink_map_gen]
      rfl)

/-! ### Splitting off a singleton summand at a source -/

instance sub_finiteDimensional (M : Diagram k o) [∀ X, FiniteDimensional k (M.obj X)]
    (A : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j))) (hA) (X : Paths (Vertex o)) :
    FiniteDimensional k ((sub M A hA).obj X) := by
  change FiniteDimensional k (A X)
  infer_instance

/-- If the outgoing maps at a source are not jointly injective, a nonzero vector in their common
kernel spans a direct summand isomorphic to the singleton interval at the source. -/
theorem exists_singleton_summand (hs : IsSource o p) (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] (hnot : ¬ OutInjective M p) :
    ∃ (N : Diagram k o) (_ : ∀ X, FiniteDimensional k (N.obj X)),
      Nonempty (M ≅ interval o (singletonInterval p) ⊞ N) ∧ totalDim N < totalDim M := by
  classical
  unfold OutInjective at hnot
  simp only [not_forall] at hnot
  obtain ⟨v, hv, hv0⟩ := hnot
  let w : Tot M := Pi.single p v
  let A : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j)) := fun j => k ∙ w j
  let C : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j)) := fun j =>
    Classical.choose (Submodule.exists_isCompl (A j))
  let B : ∀ j : Fin (n + 1), Submodule k (M.obj (vtx o j)) := fun j =>
    if j = p then C j else ⊤
  have hw : ∀ j, j ≠ p → w j = 0 := fun j hj => by simp [w, hj]
  have hA : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), A i ≤ (A j).comap (M.map (gen h)).hom := by
    intro i j h x hx
    rw [Submodule.mem_comap]
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hi : i = p
    · subst hi
      have : (M.map (gen h)).hom (w i) = 0 := by
        rw [← arr_of_arrow M h]
        simpa [w] using hv j
      rw [this]; exact Submodule.zero_mem _
    · rw [hw i hi, map_zero]; exact Submodule.zero_mem _
  have hB : ∀ {i j : Fin (n + 1)} (h : Arrow o i j), B i ≤ (B j).comap (M.map (gen h)).hom := by
    intro i j h x _
    have hj : j ≠ p := by rintro rfl; exact hs i h
    simp [B, hj]
  have hc : ∀ j, IsCompl (A j) (B j) := by
    intro j
    by_cases hj : j = p
    · simp only [B, hj, ite_true]
      subst hj
      exact Classical.choose_spec (Submodule.exists_isCompl (A j))
    · simp only [B, hj, ite_false]
      have : A j = ⊥ := by simp [A, hw j hj]
      rw [this]
      exact isCompl_bot_top
  let eA : interval (k := k) o (singletonInterval p) ≅ sub M A hA :=
    intervalIso _ _ (fun j => (⟨w j, Submodule.mem_span_singleton_self _⟩ : A j))
      (fun j x => by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
        exact ⟨c, Subtype.ext hc.symm⟩)
      (fun j hj => by
        have hjp : j = p := Fin.ext (by
          simp only [FiniteInterval.alive, singletonInterval] at hj; omega)
        subst hjp
        intro h
        have := congrArg Subtype.val h
        simp [w] at this
        exact hv0 this)
      (fun j hj => by
        have hjp : j ≠ p := fun h => hj (by
          subst h; simp [FiniteInterval.alive, singletonInterval])
        exact Subtype.ext (hw j hjp))
      (fun {i j} h hi hj => by
        exfalso
        have hi' : i.val = p.val := by
          simp only [FiniteInterval.alive, singletonInterval] at hi; omega
        have hj' : j.val = p.val := by
          simp only [FiniteInterval.alive, singletonInterval] at hj; omega
        exact h.ne (Fin.ext (hi'.trans hj'.symm)))
  refine ⟨sub M B hB, inferInstance,
    ⟨isoBiprodOfIsCompl M A B hA hB hc ≪≫ biprod.mapIso eA.symm (Iso.refl _)⟩, ?_⟩
  have := totalDim_eq_of_iso (isoBiprodOfIsCompl M A B hA hB hc ≪≫
    biprod.mapIso eA.symm (Iso.refl _))
  rw [this, totalDim_biprod]
  have := totalDim_interval_pos (k := k) (o := o) (singletonInterval p)
  omega

end TDA.Sheaf.AlternatingDiagram
