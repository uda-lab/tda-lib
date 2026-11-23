import TDA.Persistence.Morse.ReducerDiagram
import TDA.Persistence.Morse.SimplicialBridge

/-!
# The reducer run on the Morse complex of a certified matching

For a certified matching `c` of a finite input `xs`, `c.morseOccurrences` and
`c.morseDiagram p : Diagram ℤ` are `reducerOccurrences` and `reducerDiagram` of
`TDA.Persistence.Morse.ReducerDiagram` on the Morse complex `c.morseDifferential` of
`TDA.Persistence.Morse.MatchingSchedule`, with the degrees and list grades inherited by its
critical positions. They are computable and take no validity hypothesis.

On a valid input the Morse differential is a filtered differential
(`isFilteredDifferential_morseDifferential`), so the slice counts of `c.morseDiagram p` are the
ranks of the Morse persistence module (`rankOfStructureMap_eq_countP_reducerDiagram`). These
equal the ranks of the simplicial sublevel persistence module
`sublevelModule (ZMod 2) (gradeFilter xs h) p` (`rankOfStructureMap_sublevelModule_eq`), and by
`rank_sublevelHomologyMap` also the slice counts of `dgm (ZMod 2) (gradeFilter xs h) p`. Both
diagrams are positive, so `eq_reducerDiagram_of_rankCounts` gives
`c.morseDiagram p = dgm (ZMod 2) (gradeFilter xs h) p` (`morseDiagram_eq_dgm`), and with
`outputDiagram_eq_dgm` the diagram of the ordinary run of the reducer on the boundary matrix of
`xs` (`morseDiagram_eq_outputDiagram`). Two certified matchings of a valid input give the same
diagrams (`morseDiagram_eq_morseDiagram`).

Occurrence lists with the same degree-`p` points in every degree are permutations of each other
(`perm_of_degreePoints_eq`), so on a valid input `c.morseOccurrences` is a permutation of
`FiniteInput.occurrences xs`, the output of `FiniteInput.run xs` (`morseOccurrences_perm`,
`morseOccurrences_perm_of_run_eq_some`).

For a filtered differential over a field on a finite carrier, `reducerDiagram` does not depend on
the linear order of the carrier, which breaks the ties of the reducer order between generators
of equal grade and degree (`reducerDiagram_eq_of_linearOrder`), and `reducerOccurrences` depends
on it only up to permutation (`reducerOccurrences_perm_of_linearOrder`): the slice counts of
both diagrams are the ranks of the same persistence module.

This is a library derivation. It provides no interval decomposition over `ℤ`, no runtime bound
and no lifting of representatives to the input.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.ReducerDiagram

open TDA.Persistence.Reduction TDA.Persistence.Morse.Cancellation
open TDA.Persistence.Morse.ReducerOrder
open TDA.Persistence.Reduction.FiniteInput (Occurrence Death)

/-- An occurrence is determined by its degree and its point. -/
private theorem occurrence_injective :
    Function.Injective fun o : Occurrence => (o.degree, o.point) := by
  rintro ⟨d, b, e⟩ ⟨d', b', e'⟩ h
  simp only [Occurrence.point, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, he⟩ := h
  cases e <;> cases e' <;> simp_all

/-- Two occurrence lists whose degree-`p` occurrences have the same points, with multiplicity,
in every degree `p` are permutations of each other. -/
theorem perm_of_degreePoints_eq {L L' : List Occurrence}
    (h : ∀ p : ℕ,
      (((L.filter fun o => o.degree = p : List Occurrence) : Multiset Occurrence).map
        Occurrence.point) =
      (((L'.filter fun o => o.degree = p : List Occurrence) : Multiset Occurrence).map
        Occurrence.point)) :
    L.Perm L' := by
  rw [← Multiset.coe_eq_coe]
  apply Multiset.map_injective occurrence_injective
  ext ⟨p, x⟩
  have hc := congrArg (Multiset.count x) (h p)
  simp only [Multiset.count_map, ← Multiset.filter_coe, Multiset.filter_filter] at hc ⊢
  have he : ∀ o : Occurrence, ((p, x) = (o.degree, o.point)) ↔ (x = o.point ∧ o.degree = p) :=
    fun o => by rw [Prod.mk.injEq, eq_comm (a := p), and_comm]
  simpa only [he] using hc

section TieOrder

variable {ι : Type} [Fintype ι] {k : Type*} [Field k] [DecidableEq k]
  {degree : ι → ℕ} {grade : ι → ℤ} {D : Matrix ι ι k}

/-- **Tie-order independence of the reducer diagram.** For a filtered differential over a field,
`reducerDiagram` is the same for any two linear orders of the carrier. -/
theorem reducerDiagram_eq_of_linearOrder (o o' : LinearOrder ι)
    (hD : IsFilteredDifferential degree grade D) (p : ℕ) :
    @reducerDiagram ι o _ k _ _ degree grade D p =
      @reducerDiagram ι o' _ k _ _ degree grade D p :=
  @eq_reducerDiagram_of_rankCounts ι o' _ k _ _ degree grade D hD p _
    (@reducerDiagram_isPositive ι o _ k _ _ degree grade D hD p)
    fun _ _ hab => (@rankOfStructureMap_eq_countP_reducerDiagram ι o _ k _ _ degree grade D
      hD p _ _ hab).symm

/-- For a filtered differential over a field, the occurrence lists `reducerOccurrences` of any
two linear orders of the carrier are permutations of each other. -/
theorem reducerOccurrences_perm_of_linearOrder (o o' : LinearOrder ι)
    (hD : IsFilteredDifferential degree grade D) :
    (@reducerOccurrences ι o _ k _ _ degree grade D).Perm
      (@reducerOccurrences ι o' _ k _ _ degree grade D) :=
  perm_of_degreePoints_eq fun p =>
    congrArg Diagram.points (reducerDiagram_eq_of_linearOrder o o' hD p)

end TieOrder

end TDA.Persistence.Morse.ReducerDiagram

namespace TDA.Persistence.Morse.MatchingInput.CertifiedMatching

open TDA.Persistence.Reduction FiniteInput
open TDA.Persistence.Morse.Cancellation TDA.Persistence.Morse.ReducerDiagram
open TDA.Persistence.Morse.SimplicialBridge

variable {xs : Input}

/-- The occurrences of the reducer run on the Morse complex of the certificate, in the reducer
order of its critical positions. It takes no validity hypothesis and is computable. -/
def morseOccurrences (c : CertifiedMatching xs) : List Occurrence :=
  reducerOccurrences (degree xs ∘ Subtype.val) ((fun i => (xs.get i).2) ∘ Subtype.val)
    c.morseDifferential

/-- The degree-`p` diagram of the reducer run on the Morse complex of the certificate. It takes
no validity hypothesis and is computable. -/
def morseDiagram (c : CertifiedMatching xs) (p : ℕ) : Diagram ℤ :=
  reducerDiagram (degree xs ∘ Subtype.val) ((fun i => (xs.get i).2) ∘ Subtype.val)
    c.morseDifferential p

/-- On a valid input, the rank of the structure map `a ≤ b` of the simplicial sublevel
persistence module in degree `p` is the slice count of `c.morseDiagram p` at `a ≤ b`. -/
theorem rankOfStructureMap_sublevelModule_eq_countP (c : CertifiedMatching xs) (h : Valid xs)
    (p : ℕ) {a b : ℤ} (hab : a ≤ b) :
    rankOfStructureMap (sublevelModule (ZMod 2) (gradeFilter xs h) p) hab =
      (c.morseDiagram p).points.countP (fun q => q.1 ≤ a ∧ (b : WithTop ℤ) < q.2) :=
  (c.rankOfStructureMap_sublevelModule_eq h p hab).trans
    (rankOfStructureMap_eq_countP_reducerDiagram (c.isFilteredDifferential_morseDifferential h)
      p hab)

/-- On a valid input, `c.morseDiagram p` is positive. -/
theorem morseDiagram_isPositive (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ) :
    (c.morseDiagram p).IsPositive :=
  reducerDiagram_isPositive (c.isFilteredDifferential_morseDifferential h) p

/-- **The Morse run computes the sublevel diagram.** On a valid input, the degree-`p` diagram of
the reducer run on the Morse complex of a certified matching is the sublevel diagram `dgm` of the
input over `ZMod 2`. -/
theorem morseDiagram_eq_dgm (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ) :
    letI := faceFintype xs h
    c.morseDiagram p = dgm (ZMod 2) (gradeFilter xs h) p := by
  let := faceFintype xs h
  symm
  apply eq_reducerDiagram_of_rankCounts (c.isFilteredDifferential_morseDifferential h)
    (dgm_isPositive _ _ _)
  intro a b hab
  rw [← c.rankOfStructureMap_sublevelModule_eq h p hab]
  exact (rank_sublevelHomologyMap (ZMod 2) (gradeFilter xs h) p a b hab).symm

/-- **The Morse run agrees with the ordinary run.** On a valid input, the degree-`p` diagram of
the reducer run on the Morse complex of a certified matching is the diagram
`FiniteInput.outputDiagram xs p` of the reducer run on the boundary matrix of the input. -/
theorem morseDiagram_eq_outputDiagram (c : CertifiedMatching xs) (h : Valid xs) (p : ℕ) :
    c.morseDiagram p = outputDiagram xs p := by
  rw [outputDiagram_eq_dgm xs h p]
  exact c.morseDiagram_eq_dgm h p

/-- On a valid input, any two certified matchings give the same diagrams. -/
theorem morseDiagram_eq_morseDiagram (c c' : CertifiedMatching xs) (h : Valid xs) (p : ℕ) :
    c.morseDiagram p = c'.morseDiagram p :=
  (c.morseDiagram_eq_outputDiagram h p).trans (c'.morseDiagram_eq_outputDiagram h p).symm

/-- On a valid input, the occurrences of the Morse run are a permutation of the occurrences
`FiniteInput.occurrences xs` of the ordinary run. -/
theorem morseOccurrences_perm (c : CertifiedMatching xs) (h : Valid xs) :
    c.morseOccurrences.Perm (occurrences xs) :=
  perm_of_degreePoints_eq fun p => congrArg Diagram.points (c.morseDiagram_eq_outputDiagram h p)

/-- If the ordinary run `FiniteInput.run xs` returns `some L`, then the occurrences of the
Morse run of any certified matching of `xs` are a permutation of `L`. -/
theorem morseOccurrences_perm_of_run_eq_some (c : CertifiedMatching xs) {L : List Occurrence}
    (hL : run xs = some L) : c.morseOccurrences.Perm L := by
  obtain ⟨h, rfl⟩ := (run_eq_some_iff xs L).mp hL
  exact c.morseOccurrences_perm h

end TDA.Persistence.Morse.MatchingInput.CertifiedMatching
