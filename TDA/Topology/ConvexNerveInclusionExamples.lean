import TDA.Topology.ConvexNerveInclusion
import TDA.Simplicial.CollapseCertificate
import TDA.Simplicial.CollapseHomology
import TDA.Simplicial.Cone
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Inclusions of convex nerves

The three smaller intervals form a path. Extending its left interval across zero
creates a common intersection and hence a filled triangle on the same labels.
For a square annulus, enlarging one of eight open
boxes preserves a nonzero first homology group. Enlarging every box to the plane kills it.
-/

namespace TDA.Topology.ConvexNerveInclusionExamples

open Set CategoryTheory TDA.Simplicial

/-- Three open intervals with successive overlaps. -/
def pathIntervals (i : Fin 3) : Set ℝ :=
  if i = 0 then Ioo (-2) 0 else if i = 1 then Ioo (-1) 1 else Ioo 0 2

/-- Extend only the left interval, creating a triple intersection. -/
def triangleIntervals (i : Fin 3) : Set ℝ :=
  if i = 0 then Ioo (-2) (1 / 2) else pathIntervals i

/-- The path family is contained label by label in the triangle family. -/
theorem intervals_subset (i : Fin 3) : pathIntervals i ⊆ triangleIntervals i := by
  by_cases h : i = 0
  · subst i
    intro x hx
    change -2 < x ∧ x < 0 at hx
    exact ⟨hx.1, hx.2.trans (by norm_num : (0 : ℝ) < 1 / 2)⟩
  · simp [triangleIntervals, h]

/-- Both families cover the same open interval. -/
theorem intervals_iUnion_eq : (⋃ i, pathIntervals i) = ⋃ i, triangleIntervals i := by
  apply Subset.antisymm (iUnion_mono intervals_subset)
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  by_cases h : i = 0
  · subst i
    change -2 < x ∧ x < 1 / 2 at hi
    by_cases hneg : x < 0
    · exact mem_iUnion.mpr ⟨0, hi.1, hneg⟩
    · refine mem_iUnion.mpr ⟨1, ?_⟩
      change -1 < x ∧ x < 1
      constructor <;> linarith [hi.2]
  · exact mem_iUnion.mpr ⟨i, by simpa [triangleIntervals, h] using hi⟩

/-- The triple of labels is a face only after extending the left interval. -/
theorem triple_face_difference :
    Finset.univ ∈ nerve triangleIntervals ∧ Finset.univ ∉ nerve pathIntervals := by
  constructor
  · refine ⟨Finset.univ_nonempty, (1 / 4 : ℝ), ?_⟩
    intro i _
    fin_cases i <;> norm_num [triangleIntervals, pathIntervals, mem_Ioo]
  · rintro ⟨_, x, hx⟩
    have hleft : -2 < x ∧ x < 0 := hx 0 (Finset.mem_univ _)
    have hright : 0 < x ∧ x < 2 := hx 2 (Finset.mem_univ _)
    exact (lt_asymm hleft.2 hright.1)

/-- The strict labelled inclusion induces an isomorphism in each degree. -/
theorem strict_inclusion_isIso (R : Type*) [Ring R] (k : ℕ) :
    nerve pathIntervals < nerve triangleIntervals ∧
      IsIso (simplicialHomologyIncl R (nerve_mono intervals_subset) k) := by
  refine ⟨lt_of_le_not_ge (nerve_mono intervals_subset)
    (fun h => triple_face_difference.2 (h triple_face_difference.1)), ?_⟩
  apply ConvexNerve.isIso_simplicialHomologyIncl _ _ _ intervals_subset intervals_iUnion_eq
  · intro i
    unfold pathIntervals
    split_ifs <;> exact isOpen_Ioo
  · intro i
    unfold pathIntervals
    split_ifs <;> exact convex_Ioo _ _
  · intro i
    unfold triangleIntervals pathIntervals
    split_ifs <;> exact convex_Ioo _ _

namespace Annulus

open CategoryTheory.Limits
open scoped Matrix

private def box (a b c d : ℝ) : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo c d

/-- The eight open boxes around the square hole, in clockwise order starting at top left. -/
def boxes : Fin 8 → Set (ℝ × ℝ) :=
  ![box (-3) (-1) 1 3, box (-3/2) (3/2) 1 3, box 1 3 1 3, box 1 3 (-3/2) (3/2),
    box 1 3 (-3) (-1), box (-3/2) (3/2) (-3) (-1), box (-3) (-1) (-3) (-1),
    box (-3) (-1) (-3/2) (3/2)]

/-- Enlarge the top-left corner box to the entire open left column. -/
def enlargedBoxes : Fin 8 → Set (ℝ × ℝ) := Function.update boxes 0 (box (-3) (-1) (-3) 3)

private def facets : Fin 4 → Finset (Fin 8) := ![{0,1,7}, {1,2,3}, {3,4,5}, {5,6,7}]

private theorem facet_mem (j : Fin 4) : facets j ∈ nerve boxes := by
  let witnesses : Fin 4 → ℝ × ℝ := ![(-5/4,5/4), (5/4,5/4), (5/4,-5/4), (-5/4,-5/4)]
  refine ⟨by fin_cases j <;> decide, witnesses j, ?_⟩
  intro i hi
  fin_cases j <;> fin_cases i <;> norm_num [facets, witnesses, boxes, box, Set.mem_Ioo] at *

private noncomputable def quadrant (x : ℝ × ℝ) : Fin 4 :=
  if x.1 ≤ 0 then (if x.2 ≤ 0 then 3 else 0) else (if x.2 ≤ 0 then 2 else 1)

private theorem mem_facet_of_mem_box (x : ℝ × ℝ) (i : Fin 8) (hi : x ∈ boxes i) :
    i ∈ facets (quadrant x) := by
  unfold quadrant
  split_ifs <;> fin_cases i <;> first
    | decide
    | change (_ ∧ _) ∧ (_ ∧ _) at hi
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := hi
      norm_num at *
      linarith

private def sourceTable : Finset (Finset (Fin 8)) :=
  {{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7},
   {0,1}, {0,7}, {1,2}, {1,3}, {1,7}, {2,3}, {3,4}, {3,5}, {4,5}, {5,6}, {5,7}, {6,7},
   {0,1,7}, {1,2,3}, {3,4,5}, {5,6,7}}

private theorem mem_sourceTable (s : Finset (Fin 8)) : s ∈ nerve boxes ↔ s ∈ sourceTable := by
  have table : ∀ t : Finset (Fin 8), t ∈ sourceTable ↔ t.Nonempty ∧ ∃ j, t ⊆ facets j := by
    decide +kernel
  rw [table]
  constructor
  · rintro ⟨hne, x, hx⟩
    exact ⟨hne, quadrant x, fun i hi => mem_facet_of_mem_box x i (hx i hi)⟩
  · rintro ⟨hne, j, hj⟩
    exact ((nerve boxes).isRelLowerSet_faces (facet_mem j)).2 hj hne

private def cycleTable : Finset (Finset (Fin 8)) := {{1}, {3}, {5}, {7}, {1,3}, {3,5}, {5,7}, {1,7}}

private def cycleK : PreAbstractSimplicialComplex (Fin 8) :=
  FiniteComplex.toPre ⟨cycleTable, by decide +kernel, by decide +kernel⟩

-- Collapse each corner triangle across one edge, then remove its dangling corner vertex.
private theorem collapse : CollapsesTo (nerve boxes) cycleK := by
  apply collapsesTo_of_checkSteps (F := sourceTable) (T := cycleTable)
    (steps := [({0,1}, {0,1,7}), ({0}, {0,7}), ({1,2}, {1,2,3}), ({2}, {2,3}),
      ({3,4}, {3,4,5}), ({4}, {4,5}), ({5,6}, {5,6,7}), ({6}, {6,7})])
    mem_sourceTable (fun _ => Iff.rfl)
  decide +kernel

/-- The enlarged cover contains each box with its original label. -/
theorem boxes_subset (i : Fin 8) : boxes i ⊆ enlargedBoxes i := by
  by_cases h : i = 0
  · subst i
    rw [enlargedBoxes, Function.update_self]
    rintro x ⟨hx, hy⟩
    exact ⟨hx, by change 1 < x.2 ∧ x.2 < 3 at hy; exact ⟨by linarith [hy.1], hy.2⟩⟩
  · simp [enlargedBoxes, Function.update_of_ne h]

/-- The original top-left, bottom-left and left side boxes already cover the left column. -/
theorem iUnion_boxes_eq : (⋃ i, boxes i) = ⋃ i, enlargedBoxes i := by
  apply Subset.antisymm (iUnion_mono boxes_subset)
  rintro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  by_cases h : i = 0
  · subst i
    rw [enlargedBoxes, Function.update_self] at hi
    rcases hi with ⟨hx, hy⟩
    change -3 < x.2 ∧ x.2 < 3 at hy
    by_cases htop : 1 < x.2
    · exact mem_iUnion.mpr ⟨0, hx, htop, hy.2⟩
    by_cases hbot : x.2 < -1
    · exact mem_iUnion.mpr ⟨6, hx, hy.1, hbot⟩
    refine mem_iUnion.mpr ⟨7, hx, ?_⟩
    change -3/2 < x.2 ∧ x.2 < 3/2
    constructor <;> linarith
  · exact mem_iUnion.mpr ⟨i, by simpa [enlargedBoxes, Function.update_of_ne h] using hi⟩

/-- The enlarged nerve acquires the edge joining the two left corners. -/
theorem nerve_boxes_lt : nerve boxes < nerve enlargedBoxes := by
  apply lt_of_le_not_ge (nerve_mono boxes_subset)
  intro bad
  have h : ({0,6} : Finset (Fin 8)) ∈ nerve enlargedBoxes := by
    refine ⟨by decide, (-2,-2), ?_⟩
    intro i hi
    fin_cases i <;> norm_num [enlargedBoxes, boxes, box, Set.mem_Ioo, Function.update] at *
  exact (by decide +kernel : ({0,6} : Finset (Fin 8)) ∉ sourceTable) ((mem_sourceTable _).1 (bad h))

/-- The strict labelled inclusion induces an isomorphism in every degree over every ring. -/
theorem isIso_simplicialHomologyIncl (R : Type*) [Ring R] (k : ℕ) :
    IsIso (simplicialHomologyIncl R (nerve_mono boxes_subset) k) := by
  apply ConvexNerve.isIso_simplicialHomologyIncl _ _ _ boxes_subset iUnion_boxes_eq
  · intro i; fin_cases i <;> exact isOpen_Ioo.prod isOpen_Ioo
  · intro i; fin_cases i <;> exact (convex_Ioo _ _).prod (convex_Ioo _ _)
  · intro i; fin_cases i <;> simp [enlargedBoxes, Function.update] <;>
      exact (convex_Ioo _ _).prod (convex_Ioo _ _)

noncomputable section

local notation "𝔽₂" => ZMod 2

private abbrev basis {n : ℕ} (s : Face cycleK n) : Chain cycleK 𝔽₂ n := Finsupp.single s 1

private def vertex (v : Fin 8) (h : ({v} : Finset (Fin 8)) ∈ cycleTable) : Face cycleK 0 :=
  ⟨{v}, h, by simp⟩

private def edge (u v : Fin 8) (h : ({u, v} : Finset (Fin 8)) ∈ cycleTable) (huv : u < v) : Face cycleK 1 :=
  ⟨{u, v}, h, Finset.card_pair huv.ne⟩

private theorem edgeBoundary (u v : Fin 8) (hu : ({u} : Finset (Fin 8)) ∈ cycleTable)
    (hv : ({v} : Finset (Fin 8)) ∈ cycleTable) (hm : ({u, v} : Finset (Fin 8)) ∈ cycleTable) (huv : u < v) :
    boundary cycleK 𝔽₂ 0 (basis (edge u v hm huv)) = basis (vertex v hv) - basis (vertex u hu) := by
  let e := edge u v hm huv
  have he : ⇑(e.val.orderEmbOfFin e.property.2) = ![u, v] := by
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      fin_cases i <;> simp [e, edge]
    · exact Fin.strictMono_iff_lt_succ.2 (fun i => by fin_cases i; simpa using huv)
  have d0 : deletedFace cycleK 0 e 0 = vertex v hv := by
    apply Subtype.ext
    change ({u, v} : Finset (Fin 8)).erase (e.val.orderEmbOfFin e.property.2 0) = {v}
    rw [congrFun he 0]
    simp [huv.ne]
  have d1 : deletedFace cycleK 0 e 1 = vertex u hu := by
    apply Subtype.ext
    change ({u, v} : Finset (Fin 8)).erase (e.val.orderEmbOfFin e.property.2 1) = {u}
    rw [congrFun he 1]
    simp [Finset.erase_insert_of_ne, huv.ne]
  change boundary cycleK 𝔽₂ 0 (basis e) = _
  rw [boundary_single, Fin.sum_univ_two, d0, d1, sub_eq_add_neg]
  simp only [one_smul, Fin.val_zero, pow_zero, Fin.val_one, pow_one, basis, Finsupp.single_neg]

private abbrev e13 := edge 1 3 (by decide) (by decide)

private abbrev e35 := edge 3 5 (by decide) (by decide)

private abbrev e57 := edge 5 7 (by decide) (by decide)

private abbrev e17 := edge 1 7 (by decide) (by decide)

private def cycleChain : Chain cycleK 𝔽₂ 1 := basis e13 + basis e35 + basis e57 - basis e17

private def cycle : simplicialCycles cycleK 𝔽₂ 1 := ⟨cycleChain, by
  rw [simplicialCycles_succ]
  change boundary cycleK 𝔽₂ 0 cycleChain = 0
  simp only [cycleChain, map_sub, map_add]
  rw [edgeBoundary 1 3 (by decide) (by decide), edgeBoundary 3 5 (by decide) (by decide),
      edgeBoundary 5 7 (by decide) (by decide), edgeBoundary 1 7 (by decide) (by decide)]
  abel⟩

private theorem detect : cycleChain e13 = 1 := by
  have h35 : e35 ≠ e13 := fun h => (by decide : ({3,5} : Finset (Fin 8)) ≠ {1,3}) (congrArg Subtype.val h)
  have h57 : e57 ≠ e13 := fun h => (by decide : ({5,7} : Finset (Fin 8)) ≠ {1,3}) (congrArg Subtype.val h)
  have h17 : e17 ≠ e13 := fun h => (by decide : ({1,7} : Finset (Fin 8)) ≠ {1,3}) (congrArg Subtype.val h)
  simp [cycleChain, basis, h35, h57, h17]

-- No triangle survives the collapse, so every degree-two boundary is zero.
set_option backward.isDefEq.respectTransparency false in
private theorem nonzeroCycle : simplicialHomologyClass 𝔽₂ cycleK 1 cycle ≠ 0 := by
  intro hz
  have hq := congrArg
    (fun x => (homologyKernelQuotient 𝔽₂ (simplicialChainComplex cycleK 𝔽₂) 1).hom.hom x) hz
  rw [simplicialHomologyClass_quotient, map_zero] at hq
  obtain ⟨c, hc⟩ := (mem_simplicialBoundaries_iff 𝔽₂ cycleK 1 _).mp
    ((Submodule.Quotient.mk_eq_zero _).mp hq)
  have noTri : ∀ t ∈ cycleTable, t.card ≠ 3 := by decide +kernel
  have z : c = 0 := by
    ext t
    exact (noTri t.val t.property.1 t.property.2).elim
  change boundary cycleK 𝔽₂ 1 c = cycleChain at hc
  rw [z, map_zero] at hc
  exact one_ne_zero (detect.symm.trans (by rw [← hc]; rfl))

/-- The four side labels carry a nonzero first homology class over the field of two elements. -/
theorem not_isZero_homology_one : ¬ IsZero (simplicialHomology (nerve boxes) 𝔽₂ 1) := by
  intro hz
  have hz' := hz.of_iso (collapse.simplicialHomologyIso 𝔽₂ 1)
  have := ModuleCat.isZero_iff_subsingleton.mp hz'
  exact nonzeroCycle (Subsingleton.elim _ _)

/-- Eight copies of the plane on the same labels as the annulus cover. -/
def planeCover (_ : Fin 8) : Set (ℝ × ℝ) := univ

/-- Each annulus box is contained in its corresponding copy of the plane. -/
theorem boxes_subset_plane (i : Fin 8) : boxes i ⊆ planeCover i := subset_univ _

private theorem unionDiff : (⋃ i, boxes i) ≠ ⋃ i, planeCover i := by
  intro h
  have hmem : ((0,0) : (ℝ × ℝ)) ∈ ⋃ i, boxes i := h ▸ mem_iUnion.mpr ⟨0, Set.mem_univ _⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
  fin_cases i <;> norm_num [boxes, box, Set.mem_Ioo] at hi

private theorem negative : ¬ IsIso (simplicialHomologyIncl 𝔽₂ (nerve_mono boxes_subset_plane) 1) := by
  intro hi
  have eqTop : nerve planeCover = ⊤ := by
    apply le_antisymm le_top
    intro s hs
    exact ⟨hs, (0,0), fun _ _ => Set.mem_univ _⟩
  have target : IsZero (simplicialHomology (nerve planeCover) 𝔽₂ 1) := by
    rw [eqTop]
    exact isZero_simplicialHomology_top_succ 𝔽₂ 0
  exact not_isZero_homology_one
    (target.of_iso (asIso (simplicialHomologyIncl 𝔽₂ (nerve_mono boxes_subset_plane) 1)))

/-- Enlarging every box to the plane preserves convexity and openness but fills the hole.
The unions differ, and the labelled inclusion fails to induce an isomorphism in degree one. -/
theorem unequal_union_not_isIso :
    (∀ i, IsOpen (boxes i) ∧ Convex ℝ (boxes i)) ∧
    (∀ i, IsOpen (planeCover i) ∧ Convex ℝ (planeCover i)) ∧
    (⋃ i, boxes i) ≠ (⋃ i, planeCover i) ∧
    ¬ IsIso (simplicialHomologyIncl 𝔽₂ (nerve_mono boxes_subset_plane) 1) := by
  refine ⟨?_, fun _ => ⟨isOpen_univ, convex_univ⟩, unionDiff, negative⟩
  intro i
  fin_cases i <;> exact ⟨isOpen_Ioo.prod isOpen_Ioo, (convex_Ioo _ _).prod (convex_Ioo _ _)⟩

end

end Annulus

end TDA.Topology.ConvexNerveInclusionExamples
