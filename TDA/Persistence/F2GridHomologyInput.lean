import TDA.Persistence.F2GridRep
import TDA.Persistence.FiniteSimplicial
import TDA.Persistence.Reduction.FiniteInputHomologyMapCorrectness

/-!
# Rationally graded simplicial input for F₂ grid representations

A `RatGradedInput m n` is a list of faces on the vertices `Fin m`, each with a rational grade in
`Fin n → ℚ`. `RatGradedInput.Valid` is the decidable statement that the faces are nonempty and
distinct, closed under nonempty subfaces, listed after their proper faces, and graded
monotonically under face inclusion. A valid input defines a finite complex
(`RatGradedInput.toComplex`), its real grading (`RatGradedInput.toGraded`) and the actual
inclusion-induced degree-`p` homology module over F₂ (`RatGradedInput.homology`), the existing
`finiteSimplicialHomology` of that grading.

At a rational grade `u`, `RatGradedInput.slice` is the sublevel complex in the existing
one-parameter finite input format: the admitted faces, relabelled into `ℕ`, in the original
order, all at grade zero. Every slice of a valid input is valid, and its single sublevel is the actual sublevel
at the real grade of `u`, relabelled.

`RatGradedInput.toF2GridRep` is the generated F₂ grid representation in a degree `p`: the grid
values are the distinct listed grade values in each coordinate, the fiber dimension at a grade is
the length of the computed homology basis of its slice, and the matrix between two grades is the
computed matrix of the identity vertex map between their slices. The caller supplies no matrix,
rank or basis. Its validity follows from the identity and composition laws of the computed
matrices, so it needs no evaluation. The actual sublevel at a real grade equals the sublevel at
its grid floor, and is empty without a lower grid point.

For an invalid input `toF2GridRep` is still defined but carries no meaning; consumers check
`RatGradedInput.Valid` themselves. The number of parameters `n` is arbitrary because no proof
needs `n = 2`; this is a free generalisation, and only `n = 2` is exercised by examples.

This module does not identify the grid module of the generated representation with the actual
homology module; that comparison, and the erosion test for two inputs, are separate.
-/

set_option autoImplicit false

namespace TDA.Persistence

open TDA.Simplicial TDA.Filtration
open TDA.Persistence.Reduction

/-- Finite simplicial input with rational grades: a list of faces on the vertices `Fin m`, each
with a grade in `Fin n → ℚ`. -/
abbrev RatGradedInput (m n : ℕ) := List (Finset (Fin m) × (Fin n → ℚ))

namespace RatGradedInput

variable {m n : ℕ}

/-- The listed faces. -/
def faces (xs : RatGradedInput m n) : List (Finset (Fin m)) := xs.map Prod.fst

/-- Nonempty faces, no repeated face, closed under nonempty subfaces, every proper face listed
earlier, and grades monotone under face inclusion. -/
def Valid (xs : RatGradedInput m n) : Prop :=
  (∀ e ∈ xs, e.1.Nonempty) ∧
  (faces xs).Nodup ∧
  (∀ e ∈ xs, ∀ t ∈ e.1.powerset, t.Nonempty → t ∈ faces xs) ∧
  xs.Pairwise (fun e f => ¬ f.1 ⊂ e.1) ∧
  (∀ e ∈ xs, ∀ f ∈ xs, e.1 ⊆ f.1 → e.2 ≤ f.2)

instance (xs : RatGradedInput m n) : Decidable (Valid xs) := by
  unfold Valid
  infer_instance

/-- A face is listed exactly when it is the face of an entry. -/
theorem mem_faces {xs : RatGradedInput m n} {s : Finset (Fin m)} :
    s ∈ faces xs ↔ ∃ e ∈ xs, e.1 = s := by
  simp [faces]

/-! ## The actual graded complex -/

/-- The finite complex of the listed faces. -/
def toComplex (xs : RatGradedInput m n) (h : Valid xs) : FiniteComplex m where
  faces := (faces xs).toFinset
  nonempty s hs := by
    obtain ⟨e, he, rfl⟩ := mem_faces.mp (List.mem_toFinset.mp hs)
    exact h.1 e he
  downClosed {s t} hs ht hts := by
    obtain ⟨e, he, rfl⟩ := mem_faces.mp (List.mem_toFinset.mp hs)
    exact List.mem_toFinset.mpr (h.2.2.1 e he t (Finset.mem_powerset.mpr hts) ht)

/-- The complex has exactly the listed faces. -/
theorem mem_toComplex (xs : RatGradedInput m n) (h : Valid xs) (s : Finset (Fin m)) :
    s ∈ (toComplex xs h).toPre ↔ s ∈ faces xs := by
  change s ∈ (faces xs).toFinset ↔ _
  exact List.mem_toFinset

/-- The rational grade listed with a face, or zero for an unlisted face. -/
def gradeOf (xs : RatGradedInput m n) (s : Finset (Fin m)) : Fin n → ℚ :=
  ((xs.find? (fun e => decide (e.1 = s))).map Prod.snd).getD 0

/-- The grade read for a listed face is its listed grade. -/
theorem gradeOf_eq {xs : RatGradedInput m n} (h : Valid xs) {e : Finset (Fin m) × (Fin n → ℚ)}
    (he : e ∈ xs) : gradeOf xs e.1 = e.2 := by
  unfold gradeOf
  cases hf : xs.find? (fun f => decide (f.1 = e.1)) with
  | none =>
    exact absurd (List.find?_eq_none.mp hf e he) (by simp)
  | some f =>
    have hfmem := List.mem_of_find?_eq_some hf
    have hfe : f.1 = e.1 := by simpa using List.find?_some hf
    have : f = e := List.inj_on_of_nodup_map h.2.1 hfmem he hfe
    simp [this]

/-- The real grading of the listed faces. -/
def toGraded (xs : RatGradedInput m n) (h : Valid xs) : FiniteGraded (toComplex xs h) n where
  grade s := RatGrid.realGrade (gradeOf xs s.val)
  mono {s t} hst := by
    obtain ⟨e, he, hes⟩ := mem_faces.mp ((mem_toComplex xs h s.val).mp s.property)
    obtain ⟨f, hf, hft⟩ := mem_faces.mp ((mem_toComplex xs h t.val).mp t.property)
    rw [RatGrid.realGrade_le_iff, ← hes, ← hft, gradeOf_eq h he, gradeOf_eq h hf]
    exact h.2.2.2.2 e he f hf (hes ▸ hft ▸ hst)

/-- The real grade of a face is the real image of its rational grade. -/
theorem toGraded_grade (xs : RatGradedInput m n) (h : Valid xs)
    (s : TotalFace (toComplex xs h).toPre) :
    (toGraded xs h).grade s = RatGrid.realGrade (gradeOf xs s.val) := rfl

/-- A sublevel of the actual grading consists of the listed faces with grade below the
threshold. -/
theorem mem_sublevel_toGraded_iff (xs : RatGradedInput m n) (h : Valid xs) (a : Fin n → ℝ)
    (s : Finset (Fin m)) :
    s ∈ (toGraded xs h).sublevel a ↔ ∃ e ∈ xs, e.1 = s ∧ RatGrid.realGrade e.2 ≤ a := by
  constructor
  · rintro ⟨hs, hle⟩
    obtain ⟨e, he, rfl⟩ := mem_faces.mp ((mem_toComplex xs h s).mp hs)
    refine ⟨e, he, rfl, ?_⟩
    have hg : (toGraded xs h).grade ⟨e.1, hs⟩ = RatGrid.realGrade e.2 := by
      rw [toGraded_grade, gradeOf_eq h he]
    exact hg ▸ hle
  · rintro ⟨e, he, rfl, hle⟩
    have hs : e.1 ∈ (toComplex xs h).toPre :=
      (mem_toComplex xs h e.1).mpr (mem_faces.mpr ⟨e, he, rfl⟩)
    refine ⟨hs, ?_⟩
    have hg : (toGraded xs h).grade ⟨e.1, hs⟩ = RatGrid.realGrade e.2 := by
      rw [toGraded_grade, gradeOf_eq h he]
    exact hg ▸ hle

/-- The actual inclusion-induced degree-`p` homology over F₂ of the rationally graded input. -/
noncomputable abbrev homology (xs : RatGradedInput m n) (h : Valid xs) (p : ℕ) :
    PModule.{0,0,0} (ZMod 2) (Fin n → ℝ) :=
  finiteSimplicialHomology (ZMod 2) (toGraded xs h) p

/-! ## Slices in the existing finite input format -/

/-- The sublevel complex at a rational grade, as a one-parameter finite input: the admitted
faces, relabelled into `ℕ`, in the original order, all at grade zero. -/
def slice (xs : RatGradedInput m n) (u : Fin n → ℚ) : FiniteInput.Input :=
  (xs.filter (fun e => decide (e.2 ≤ u))).map (fun e => (e.1.map Fin.valEmbedding, 0))

/-- The entries of a slice are the relabelled admitted faces at grade zero. -/
theorem mem_slice {xs : RatGradedInput m n} {u : Fin n → ℚ} {x : Finset ℕ × ℤ} :
    x ∈ slice xs u ↔ ∃ e ∈ xs, e.2 ≤ u ∧ (e.1.map Fin.valEmbedding, (0 : ℤ)) = x := by
  simp [slice, and_assoc]

private theorem slice_faces (xs : RatGradedInput m n) (u : Fin n → ℚ) :
    FiniteInput.faces (slice xs u) =
      ((xs.filter (fun e => decide (e.2 ≤ u))).map Prod.fst).map
        (Finset.map Fin.valEmbedding) := by
  simp [FiniteInput.faces, slice, List.map_map, Function.comp_def]

/-- Every slice is a valid finite input. -/
theorem slice_valid {xs : RatGradedInput m n} (h : Valid xs) (u : Fin n → ℚ) :
    FiniteInput.Valid (slice xs u) := by
  obtain ⟨hne, hnd, hcl, hord, hmono⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨e, he, -, hx⟩ := mem_slice.mp (List.get_mem (slice xs u) i)
    rw [← hx]
    exact (hne e he).map
  · rw [slice_faces]
    exact ((hnd.sublist ((List.filter_sublist).map Prod.fst)).map
      (Finset.map_injective Fin.valEmbedding))
  · intro i t ht htne
    obtain ⟨e, he, heu, hx⟩ := mem_slice.mp (List.get_mem (slice xs u) i)
    rw [← hx] at ht
    obtain ⟨t', ht'e, rfl⟩ := Finset.subset_map_iff.mp (Finset.mem_powerset.mp ht)
    have ht'ne : t'.Nonempty := Finset.map_nonempty.mp htne
    obtain ⟨f, hf, hft⟩ := mem_faces.mp (hcl e he t' (Finset.mem_powerset.mpr ht'e) ht'ne)
    have hfu : f.2 ≤ u := (hmono f hf e he (hft ▸ ht'e)).trans heu
    rw [FiniteInput.faces, List.mem_map]
    exact ⟨_, mem_slice.mpr ⟨f, hf, hfu, rfl⟩, by simp [hft]⟩
  · have hpw : (slice xs u).Pairwise (fun x y => ¬ y.1 ⊂ x.1) := by
      unfold slice
      rw [List.pairwise_map]
      refine (hord.filter _).imp ?_
      intro e f hef
      simpa [Finset.map_ssubset_map] using hef
    intro i j hij
    by_contra hji
    rcases (not_lt.mp hji).lt_or_eq with hlt | heq
    · exact (List.pairwise_iff_get.mp hpw j i hlt) hij
    · subst heq
      exact (lt_irrefl _) hij
  · intro i j _
    obtain ⟨_, _, _, hi⟩ := mem_slice.mp (List.get_mem (slice xs u) i)
    obtain ⟨_, _, _, hj⟩ := mem_slice.mp (List.get_mem (slice xs u) j)
    rw [← hi, ← hj]

/-- The single sublevel of a slice is the actual sublevel at the real grade, relabelled. -/
theorem mem_sublevel_slice_iff {xs : RatGradedInput m n} (h : Valid xs) (u : Fin n → ℚ)
    (s : Finset ℕ) :
    s ∈ (FiniteInput.gradeFilter (slice xs u) (slice_valid h u)).sublevel 0 ↔
      ∃ t ∈ (toGraded xs h).sublevel (RatGrid.realGrade u), t.map Fin.valEmbedding = s := by
  rw [FiniteInput.mem_sublevel_iff_list]
  constructor
  · rintro ⟨i, hi, -⟩
    obtain ⟨e, he, heu, hx⟩ := mem_slice.mp (List.get_mem (slice xs u) i)
    refine ⟨e.1, (mem_sublevel_toGraded_iff xs h _ _).mpr
      ⟨e, he, rfl, RatGrid.realGrade_le_iff.mpr heu⟩, ?_⟩
    rw [← hi, ← hx]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨e, he, rfl, heu⟩ := (mem_sublevel_toGraded_iff xs h _ _).mp ht
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp
      (mem_slice.mpr ⟨e, he, RatGrid.realGrade_le_iff.mp heu, rfl⟩)
    exact ⟨i, by rw [hi], by rw [hi]⟩

/-- Identity on vertices maps each slice into every later slice. -/
theorem vertexMapCondition_slice {xs : RatGradedInput m n} {u v : Fin n → ℚ} (huv : u ≤ v) :
    FiniteInput.VertexMapCondition (slice xs u) (slice xs v) 0 0 id := by
  intro i _
  obtain ⟨e, he, heu, hx⟩ := mem_slice.mp (List.get_mem (slice xs u) i)
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (mem_slice.mpr ⟨e, he, heu.trans huv, rfl⟩)
  refine ⟨j, ?_, ?_⟩
  · rw [hj, ← hx, Finset.image_id]
  · rw [hj]

/-! ## The generated F₂ grid representation -/

/-- The distinct listed grade values in each coordinate. -/
def gridValues (xs : RatGradedInput m n) : RatGrid n := fun i => (xs.map fun e => e.2 i).dedup

/-- A grid value is a listed grade value in that coordinate. -/
theorem mem_gridValues {xs : RatGradedInput m n} {i : Fin n} {q : ℚ} :
    q ∈ gridValues xs i ↔ ∃ e ∈ xs, e.2 i = q := by
  simp [gridValues]

/-- Every listed grade is a grid grade. -/
theorem grade_mem_points {xs : RatGradedInput m n} {e : Finset (Fin m) × (Fin n → ℚ)}
    (he : e ∈ xs) : e.2 ∈ (gridValues xs).points :=
  (RatGrid.mem_points (gridValues xs)).mpr fun _ => mem_gridValues.mpr ⟨e, he, rfl⟩

/-- Every listed face lies below a real threshold exactly when it lies below the grid floor of
that threshold. -/
theorem sublevel_floor {xs : RatGradedInput m n} (h : Valid xs) (a : Fin n → ℝ)
    (ha : (gridValues xs).grid.HasLowerPoint a) :
    (toGraded xs h).sublevel ((gridValues xs).grid.embedding ((gridValues xs).grid.floor a ha)) =
      (toGraded xs h).sublevel a := by
  apply (toGraded xs h).sublevel_eq_of_forall_le_iff
  intro s
  refine ⟨fun hs => hs.trans ((gridValues xs).grid.floor_le a ha), fun hs => ?_⟩
  obtain ⟨e, he, hes⟩ := mem_faces.mp ((mem_toComplex xs h s.val).mp s.property)
  have hg : (toGraded xs h).grade s =
      (gridValues xs).grid.embedding ((gridValues xs).pointOfRat e.2 (grade_mem_points he)) := by
    rw [RatGrid.embedding_pointOfRat, toGraded_grade, ← hes, gradeOf_eq h he]
  rw [hg] at hs ⊢
  exact (gridValues xs).grid.embedding.monotone ((gridValues xs).grid.le_floor a ha hs)

/-- Without a lower grid point no listed face is present; when `n ≥ 1` this covers empty
input. -/
theorem sublevel_eq_bot_of_not_hasLowerPoint {xs : RatGradedInput m n} (h : Valid xs)
    (a : Fin n → ℝ) (ha : ¬ (gridValues xs).grid.HasLowerPoint a) :
    (toGraded xs h).sublevel a = ⊥ := by
  apply ((toGraded xs h).sublevel_eq_bot_iff a).mpr
  intro s hs
  obtain ⟨e, he, hes⟩ := mem_faces.mp ((mem_toComplex xs h s.val).mp s.property)
  refine ha ⟨(gridValues xs).pointOfRat e.2 (grade_mem_points he), ?_⟩
  rw [RatGrid.embedding_pointOfRat, ← gradeOf_eq h he, hes]
  exact hs

/-- The generated F₂ grid representation in degree `p`: the fiber dimension at a grade is the
length of the computed basis of its slice, and the matrix between two grades is the computed
matrix of the identity vertex map between their slices. -/
def toF2GridRep (xs : RatGradedInput m n) (p : ℕ) : F2GridRep n where
  values := gridValues xs
  dim u := (FiniteInput.activeRepresentatives (slice xs u) p 0).length
  map u v := FiniteInput.homologyMapMatrix (slice xs u) (slice xs v) p 0 0 id

/-- The generated matrix from a grade to itself is the identity. -/
theorem toF2GridRep_map_self {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ)
    (u : Fin n → ℚ) : (toF2GridRep xs p).map u u = 1 :=
  FiniteInput.homologyMapMatrix_id _ (slice_valid h u) p 0

/-- The generated matrices compose along comparable triples of grades. -/
theorem toF2GridRep_map_comp {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ)
    {u v w : Fin n → ℚ} (huv : u ≤ v) (hvw : v ≤ w) :
    (toF2GridRep xs p).map v w * (toF2GridRep xs p).map u v = (toF2GridRep xs p).map u w :=
  (FiniteInput.homologyMapMatrix_comp _ _ _ (slice_valid h u) (slice_valid h v)
    (slice_valid h w) p 0 0 0 id id (vertexMapCondition_slice huv)
    (vertexMapCondition_slice hvw)).symm

/-- The generated representation of valid input is valid. -/
theorem toF2GridRep_valid {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ) :
    (toF2GridRep xs p).Valid :=
  ⟨fun u _ => toF2GridRep_map_self h p u,
    fun _ _ _ _ _ _ huv hvw => toF2GridRep_map_comp h p huv hvw⟩

end RatGradedInput

end TDA.Persistence
