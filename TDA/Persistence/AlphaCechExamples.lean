import TDA.Filtration.RationalAlpha
import TDA.Persistence.AlphaCech
import TDA.Simplicial.VertexChainMap
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-!
# A five-point α–Čech persistence square

At squared grade four the α nerve is a cycle and the Čech nerve contains an additional
filled triangle on the same labels. At grade five both nerves contain the triangle.
The coefficient of BC detects the same nonzero F₂ class in all four complexes.
-/

namespace TDA.Persistence.AlphaCechExamples

open CategoryTheory TDA.Filtration TDA.Filtration.RationalAlpha TDA.Simplicial
open scoped Matrix
noncomputable section

/-- The labelled points A, B, C, D, E in the rational plane, in that order. -/
def cloud : Fin 5 ↪ Point where
  toFun := ![(0, 0), (4, 0), (4, 4), (0, 4), (1, -1)]
  inj' := by decide +kernel

/-- The five vertices and the five cycle edges. -/
def cycleFaces : Finset (Finset (Fin 5)) :=
  {{0}, {1}, {2}, {3}, {4}, {0, 4}, {1, 4}, {1, 2}, {2, 3}, {0, 3}}

/-- Add the edge AB and its unique incident triangle ABE. -/
def enlargedFaces : Finset (Finset (Fin 5)) :=
  insert {0, 1} (insert {0, 1, 4} cycleFaces)

private def tableAt (q : ℚ) : Finset (Finset (Fin 5)) :=
  ((gradedFaces cloud).filter (fun row => row.2 ≤ q)).image Prod.fst

private theorem tableAt_four : tableAt 4 = cycleFaces := by decide +kernel

private theorem tableAt_five : tableAt 5 = enlargedFaces := by decide +kernel

private theorem same_geometric_faces (s : Finset (Fin 5)) (q : ℚ) :
    s ∈ Alpha.complex (realSites cloud) (q : ℝ) ↔ s ∈ tableAt q := by
  rw [RationalAlpha.mem_complex_iff]
  simp only [tableAt, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨r, hr, hq⟩
    exact ⟨s, r.grade, ⟨(mem_gradedFaces_iff cloud r.grade).2 ⟨r, hr, rfl⟩,
      by exact_mod_cast hq⟩, rfl⟩
  · rintro ⟨s', q', ⟨hrow, hle⟩, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (mem_gradedFaces_iff cloud q').1 hrow
    exact ⟨r, hr, by exact_mod_cast hle⟩

/-- Exactly the cycle is present at squared grade four. -/
theorem alpha_faces_four (s : Finset (Fin 5)) :
    s ∈ Alpha.complex (realSites cloud) 4 ↔ s ∈ cycleFaces := by
  simpa only [tableAt_four, Rat.cast_ofNat] using same_geometric_faces s 4

/-- The edge AB and triangle ABE join the cycle at squared grade five. -/
theorem alpha_faces_five (s : Finset (Fin 5)) :
    s ∈ Alpha.complex (realSites cloud) 5 ↔ s ∈ enlargedFaces := by
  simpa only [tableAt_five, Rat.cast_ofNat] using same_geometric_faces s 5

/-- The center (2, 0) witnesses all three labels at squared grade four. -/
theorem cech_triangle_four : ({0, 1, 4} : Finset (Fin 5)) ∈
    Cech.complex (realSites cloud) (Real.sqrt 4) := by
  apply (Cech.mem_complex_iff _ _ _).2
  refine ⟨by decide, castPoint (2, 0), ?_⟩
  intro i hi
  apply (Real.le_sqrt dist_nonneg (by norm_num)).2
  change dist (castPoint (2, 0)) (castPoint (cloud i)) ^ 2 ≤ 4
  rw [distSq_cast]
  have h : sqDist (2, 0) (cloud i) ≤ (4 : ℚ) := by
    have hm : i = 0 ∨ i = 1 ∨ i = 4 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
    rcases hm with rfl | rfl | rfl <;> decide +kernel
  exact_mod_cast h

private theorem pairwise_test (s : Finset (Fin 5)) (hn : s.Nonempty)
    (h : ∀ i ∈ s, ∀ j ∈ s, sqDist (cloud i) (cloud j) ≤ 20) :
    s ∈ enlargedFaces := by
  have all : ∀ a : Finset (Fin 5), a.Nonempty →
      (∀ i ∈ a, ∀ j ∈ a, sqDist (cloud i) (cloud j) ≤ 20) →
      a ∈ enlargedFaces := by decide +kernel
  exact all s hn h

/-- The Čech face table is constant from squared grade four through five. -/
theorem cech_faces_between {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5)
    (s : Finset (Fin 5)) :
    s ∈ Cech.complex (realSites cloud) (Real.sqrt t) ↔ s ∈ enlargedFaces := by
  have ht : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 4).trans ht4
  constructor
  · intro h
    apply pairwise_test s ((Cech.mem_complex_iff _ _ _).1 h).1
    intro i hi j hj
    have hd := Cech.dist_le_two_mul_of_mem_complex _ h hi hj
    have hd' := (sq_le_sq₀ dist_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg t))).mpr hd
    rw [mul_pow, Real.sq_sqrt ht] at hd'
    change dist (castPoint (cloud i)) (castPoint (cloud j)) ^ 2 ≤ _ at hd'
    rw [distSq_cast] at hd'
    have hreal : (sqDist (cloud i) (cloud j) : ℝ) ≤ 20 := by linarith
    exact_mod_cast hreal
  · intro h
    apply Cech.complex_mono (realSites cloud) (Real.sqrt_monotone ht4)
    simp only [enlargedFaces, Finset.mem_insert] at h
    rcases h with rfl | rfl | h
    · apply ((Cech.complex (realSites cloud) (Real.sqrt 4)).isRelLowerSet_faces
        cech_triangle_four).2
      · decide
      · decide
    · exact cech_triangle_four
    · exact Alpha.filtration_le_cech (realSites cloud) 4 ((alpha_faces_four s).2 h)

local notation "KType" => PreAbstractSimplicialComplex (Fin 5)
/-- The complex contains the five vertices and edges of the designated cycle. -/
abbrev HasCycle (K : KType) := ∀ s ∈ cycleFaces, s ∈ K

private def vertex {K : KType} (h : HasCycle K) (v : Fin 5) : Face K 0 :=
  ⟨{v}, h _ (by fin_cases v <;> decide +kernel), by simp⟩

private def edge {K : KType} (h : HasCycle K) (u v : Fin 5)
    (hm : ({u, v} : Finset (Fin 5)) ∈ cycleFaces) (hne : u < v) : Face K 1 :=
  ⟨{u, v}, h _ hm, Finset.card_pair hne.ne⟩

private abbrev eAE {K : KType} (h : HasCycle K) := edge h 0 4 (by decide) (by decide)
private abbrev eBE {K : KType} (h : HasCycle K) := edge h 1 4 (by decide) (by decide)
private abbrev eBC {K : KType} (h : HasCycle K) := edge h 1 2 (by decide) (by decide)
private abbrev eCD {K : KType} (h : HasCycle K) := edge h 2 3 (by decide) (by decide)
private abbrev eAD {K : KType} (h : HasCycle K) := edge h 0 3 (by decide) (by decide)

/-- The unit F₂ chain of an ordered face. -/
abbrev basis {K : KType} {n : ℕ} (s : Face K n) : Chain K (ZMod 2) n := Finsupp.single s 1

private theorem boundary_edge {K : KType} (h : HasCycle K) {u v : Fin 5}
    (hm : ({u, v} : Finset (Fin 5)) ∈ cycleFaces) (huv : u < v) :
    boundary K (ZMod 2) 0 (basis (edge h u v hm huv)) =
      basis (vertex h v) - basis (vertex h u) := by
  let e := edge h u v hm huv
  have he : ⇑(e.val.orderEmbOfFin e.property.2) = ![u, v] := by
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      fin_cases i <;> simp [e, edge]
    · exact Fin.strictMono_iff_lt_succ.2 (fun i => by fin_cases i; simpa using huv)
  have d0 : deletedFace K 0 e 0 = vertex h v := by
    apply Subtype.ext
    change ({u, v} : Finset (Fin 5)).erase (e.val.orderEmbOfFin e.property.2 0) = {v}
    rw [congrFun he 0]
    simp [huv.ne]
  have d1 : deletedFace K 0 e 1 = vertex h u := by
    apply Subtype.ext
    change ({u, v} : Finset (Fin 5)).erase (e.val.orderEmbOfFin e.property.2 1) = {u}
    rw [congrFun he 1]
    simp [Finset.erase_insert_of_ne, huv.ne]
  change boundary K (ZMod 2) 0 (basis e) = _
  rw [boundary_single, Fin.sum_univ_two, d0, d1, sub_eq_add_neg]
  simp only [one_smul, Fin.val_zero, pow_zero, Fin.val_one, pow_one, basis, Finsupp.single_neg]

private def rawCycle {K : KType} (h : HasCycle K) : Chain K (ZMod 2) 1 :=
  basis (eAE h) - basis (eBE h) + basis (eBC h) + basis (eCD h) - basis (eAD h)

private def cycle {K : KType} (h : HasCycle K) : simplicialCycles K (ZMod 2) 1 :=
  ⟨rawCycle h, by
    rw [simplicialCycles_succ]
    change boundary K (ZMod 2) 0 (rawCycle h) = 0
    simp only [rawCycle, map_sub, map_add, boundary_edge]
    abel⟩

-- No triangle touches BC, so evaluating that edge detects the homology class.
private theorem noTriangleOnBC (s : Finset (Fin 5)) (hc : s.card = 3)
    (hm : s ∈ enlargedFaces) : ¬ ({1, 2} : Finset (Fin 5)) ⊆ s := by
  have all : ∀ t : Finset (Fin 5), t.card = 3 → t ∈ enlargedFaces →
      ¬ ({1, 2} : Finset (Fin 5)) ⊆ t := by decide +kernel
  exact all s hc hm

set_option backward.isDefEq.respectTransparency false in
private theorem cycle_class_nonzero {K : KType} (h : HasCycle K)
    (hcap : ∀ s ∈ K, s ∈ enlargedFaces) :
    simplicialHomologyClass (ZMod 2) K 1 (cycle h) ≠ 0 := by
  intro hz
  have hq := congrArg
    (fun x => (homologyKernelQuotient (ZMod 2) (simplicialChainComplex K (ZMod 2)) 1).hom.hom x) hz
  rw [simplicialHomologyClass_quotient, map_zero] at hq
  obtain ⟨c, hc⟩ := (mem_simplicialBoundaries_iff (ZMod 2) K 1 _).mp
    ((Submodule.Quotient.mk_eq_zero _).mp hq)
  let f : Chain K (ZMod 2) 1 →ₗ[ZMod 2] ZMod 2 := Finsupp.lapply (eBC h)
  have hf : f.comp (boundary K (ZMod 2) 1) = 0 := by
    apply Finsupp.lhom_ext
    intro t a
    change f (boundary K (ZMod 2) 1 (Finsupp.single t a)) = 0
    have hn (i : Fin 3) : deletedFace K 1 t i ≠ eBC h := by
      intro he
      have hsub : (deletedFace K 1 t i).val ⊆ t.val := Finset.erase_subset _ _
      rw [he] at hsub
      exact noTriangleOnBC t.val t.property.2 (hcap _ t.property.1) hsub
    rw [boundary_single, map_smul, map_sum]
    simp [f, hn]
  have h1 : f (rawCycle h) = 1 := by
    have nAE : eAE h ≠ eBC h := fun he => (by decide : ({0, 4} : Finset (Fin 5)) ≠ {1, 2})
      (congrArg Subtype.val he)
    have nBE : eBE h ≠ eBC h := fun he => (by decide : ({1, 4} : Finset (Fin 5)) ≠ {1, 2})
      (congrArg Subtype.val he)
    have nCD : eCD h ≠ eBC h := fun he => (by decide : ({2, 3} : Finset (Fin 5)) ≠ {1, 2})
      (congrArg Subtype.val he)
    have nAD : eAD h ≠ eBC h := fun he => (by decide : ({0, 3} : Finset (Fin 5)) ≠ {1, 2})
      (congrArg Subtype.val he)
    simp only [rawCycle, map_sub, map_add, f, Finsupp.lapply_apply, basis,
      Finsupp.single_apply, nAE, nBE, nCD, nAD, ite_false, ite_true,
      sub_zero, add_zero, zero_add]
  have h0 : f (boundary K (ZMod 2) 1 c) = 0 := by
    exact DFunLike.congr_fun hf c
  change boundary K (ZMod 2) 1 c = rawCycle h at hc
  rw [hc, h1] at h0
  exact one_ne_zero h0

private theorem inclusion_preserves_cycle_class {K L : KType} (hK : HasCycle K) (hL : HasCycle L)
    (i : K ≤ L) :
    (simplicialHomologyIncl (ZMod 2) i 1).hom
        (simplicialHomologyClass (ZMod 2) K 1 (cycle hK)) =
      simplicialHomologyClass (ZMod 2) L 1 (cycle hL) := by
  rw [← simplicialHomologyMap_inclusion]
  apply simplicialHomologyMap_class
  rw [vertexChainMap_inclusion]
  change chainIncl (ZMod 2) i 1 (rawCycle hK) = rawCycle hL
  simp only [rawCycle, map_add, map_sub, chainIncl_single, basis]
  rfl

/-- E forces the common Voronoi cells of A and B above height one on their bisector. -/
theorem cellsAB (x : Plane) (hx : x ∈ Alpha.commonCells (realSites cloud) {0, 1}) :
    x 0 = 2 ∧ 1 ≤ x 1 := by
  obtain ⟨h, q⟩ := (mem_commonCells_iff cloud (v := 0) (by decide : (0 : Fin 5) ∈ ({0, 1} : Finset (Fin 5))) x).1 hx
  have eq := q 1 (by decide)
  have lo := h 4
  norm_num [cloud, linearForm, normal, offset] at eq lo
  constructor <;> linarith

/-- The point (2, 1) belongs to all three closed cells at squared distance five from A. -/
theorem witnessFive : castPoint (2, 1) ∈ Alpha.commonCells (realSites cloud) {0, 1, 4} ∧
    dist (castPoint (2, 1)) (realSites cloud 0) ^ 2 = 5 := by
  constructor
  · intro v hv j
    apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
    change dist (castPoint (2, 1)) (castPoint (cloud v)) ^ 2 ≤ dist (castPoint (2, 1)) (castPoint (cloud j)) ^ 2
    rw [distSq_cast, distSq_cast]
    have all : ∀ v ∈ ({0, 1, 4} : Finset (Fin 5)), ∀ j, sqDist (2, 1) (cloud v) ≤ sqDist (2, 1) (cloud j) := by decide +kernel
    exact_mod_cast all v hv j
  · change dist (castPoint (2, 1)) (castPoint (cloud 0)) ^ 2 = 5
    rw [distSq_cast]
    exact_mod_cast (by decide +kernel : sqDist (2, 1) (cloud 0) = (5 : ℚ))

/-- The enlarged face table has a single triangle, so all 2-boundaries are multiples
of its signed boundary. Over F₂ the only coefficients are zero and one. -/
theorem onlyTriangleBoundaries (K : KType) (hK : ∀ s, s ∈ K ↔ s ∈ enlargedFaces) :
    ∃ tri : Face K 2, tri.val = {0, 1, 4} ∧
      ∀ c : Chain K (ZMod 2) 2,
        boundary K (ZMod 2) 1 c = 0 ∨
        boundary K (ZMod 2) 1 c = boundary K (ZMod 2) 1 (basis tri) := by
  classical
  let tri : Face K 2 := ⟨{0, 1, 4}, (hK _).2 (by decide), by decide⟩
  have hall : ∀ s : Finset (Fin 5), s ∈ enlargedFaces → s.card = 3 → s = {0, 1, 4} := by decide +kernel
  have same (t : Face K 2) : t = tri := Subtype.ext (hall _ ((hK _).1 t.property.1) t.property.2)
  refine ⟨tri, rfl, fun c => ?_⟩
  have hc : c = Finsupp.single tri (c tri) := by
    ext t
    rw [same t, Finsupp.single_eq_same]
  have z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases z2 (c tri) with h | h
  · left
    rw [hc, h, Finsupp.single_zero, map_zero]
  · right
    rw [hc, h]

/-- The boundary of the unique triangle ABE over F₂ is BE + AE + AB. -/
theorem boundaryABE (K : KType) (hK : ∀ s, s ∈ K ↔ s ∈ enlargedFaces) :
    let face (s : Finset (Fin 5)) (hm : s ∈ enlargedFaces) (hc : s.card = 2) : Face K 1 :=
      ⟨s, (hK s).2 hm, hc⟩
    let tri : Face K 2 := ⟨{0, 1, 4}, (hK _).2 (by decide), by decide⟩
    boundary K (ZMod 2) 1 (basis tri) =
      basis (face {1, 4} (by decide) (by decide)) +
      basis (face {0, 4} (by decide) (by decide)) +
      basis (face {0, 1} (by decide) (by decide)) := by
  dsimp only
  let tri : Face K 2 := ⟨{0, 1, 4}, (hK _).2 (by decide), by decide⟩
  let ab : Face K 1 := ⟨{0, 1}, (hK _).2 (by decide), by decide⟩
  let ae : Face K 1 := ⟨{0, 4}, (hK _).2 (by decide), by decide⟩
  let be : Face K 1 := ⟨{1, 4}, (hK _).2 (by decide), by decide⟩
  change boundary K (ZMod 2) 1 (basis tri) = basis be + basis ae + basis ab
  have order : ⇑(tri.val.orderEmbOfFin tri.property.2) = ![(0 : Fin 5), 1, 4] := by
    symm
    apply Finset.orderEmbOfFin_unique
    · intro i
      change ![(0 : Fin 5), 1, 4] i ∈ ({0, 1, 4} : Finset (Fin 5))
      fin_cases i <;> decide
    · exact Fin.strictMono_iff_lt_succ.2 (fun i => by fin_cases i <;> decide)
  have d0 : deletedFace K 1 tri 0 = be := by
    apply Subtype.ext
    change ({0, 1, 4} : Finset (Fin 5)).erase (tri.val.orderEmbOfFin tri.property.2 0) = {1, 4}
    rw [congrFun order 0]
    decide
  have d1 : deletedFace K 1 tri 1 = ae := by
    apply Subtype.ext
    change ({0, 1, 4} : Finset (Fin 5)).erase (tri.val.orderEmbOfFin tri.property.2 1) = {0, 4}
    rw [congrFun order 1]
    decide
  have d2 : deletedFace K 1 tri 2 = ab := by
    apply Subtype.ext
    change ({0, 1, 4} : Finset (Fin 5)).erase (tri.val.orderEmbOfFin tri.property.2 2) = {0, 1}
    rw [congrFun order 2]
    decide
  rw [basis, boundary_single, Fin.sum_univ_three, d0, d1, d2]
  have minus : (-1 : ZMod 2) = 1 := by decide
  simp [minus, basis]


local notation "Fα" => Alpha.labelledComplexFiltration (realSites cloud)
local notation "FČ" => Alpha.squaredCechFiltration (realSites cloud)
local notation "Hα" => simplicialHomologyPModule (ZMod 2) Fα 1
local notation "HČ" => simplicialHomologyPModule (ZMod 2) FČ 1

private theorem hasAlphaFour : HasCycle (Fα 4) := fun s hs => (alpha_faces_four s).2 hs
private theorem hasAlphaFive : HasCycle (Fα 5) :=
  fun s hs => (Fα).monotone (by norm_num : (4 : ℝ) ≤ 5) (hasAlphaFour s hs)
private theorem hasCechFour : HasCycle (FČ 4) :=
  fun s hs => Alpha.labelledComplexFiltration_le_squaredCech _ 4 (hasAlphaFour s hs)
private theorem hasCechFive : HasCycle (FČ 5) :=
  fun s hs => Alpha.labelledComplexFiltration_le_squaredCech _ 5 (hasAlphaFive s hs)
private theorem capAlphaFive : ∀ s ∈ Fα 5, s ∈ enlargedFaces := fun s hs => (alpha_faces_five s).1 hs
private theorem capCechFive : ∀ s ∈ FČ 5, s ∈ enlargedFaces := by
  rw [Alpha.squaredCechFiltration_apply_of_nonneg _ (by norm_num)]
  exact fun s hs => (cech_faces_between (by norm_num) le_rfl s).1 hs

/-- The F₂ class represented by the oriented cycle AE, EB, BC, CD, DA. -/
def cycleClass {K : KType} (h : HasCycle K) : simplicialHomology K (ZMod 2) 1 :=
  simplicialHomologyClass (ZMod 2) K 1 (cycle h)

/-- The Čech triangle ABE is absent from α at squared grade four. -/
theorem strictAtFour : Fα 4 < FČ 4 := by
  apply lt_of_le_not_ge (Alpha.labelledComplexFiltration_le_squaredCech _ 4)
  intro h
  have hlarge : ({0, 1, 4} : Finset (Fin 5)) ∈ FČ 4 := by
    rw [Alpha.squaredCechFiltration_apply_of_nonneg _ (by norm_num)]
    exact cech_triangle_four
  exact (by decide +kernel : ({0, 1, 4} : Finset (Fin 5)) ∉ cycleFaces)
    ((alpha_faces_four _).1 (h hlarge))

/-- The class is nonzero at all four corners. Each structure map and each component of
the natural isomorphism carries the cycle to its namesake. -/
theorem fivePointH1Square :
    let e := alphaCechIso (realSites cloud) (ZMod 2) 1
    let step := homOfLE (by norm_num : (4 : ℝ) ≤ 5)
    let a₄ := cycleClass hasAlphaFour
    let a₅ := cycleClass hasAlphaFive
    let c₄ := cycleClass hasCechFour
    let c₅ := cycleClass hasCechFive
    a₄ ≠ 0 ∧ a₅ ≠ 0 ∧ c₄ ≠ 0 ∧ c₅ ≠ 0 ∧
      ((Hα).map step).hom a₄ = a₅ ∧ ((HČ).map step).hom c₄ = c₅ ∧
      (e.hom.app 4).hom a₄ = c₄ ∧ (e.hom.app 5).hom a₅ = c₅ := by
  have h45 : (4 : ℝ) ≤ 5 := by norm_num
  exact ⟨cycle_class_nonzero hasAlphaFour (fun s hs => capAlphaFive s ((Fα).monotone h45 hs)),
    cycle_class_nonzero hasAlphaFive capAlphaFive,
    cycle_class_nonzero hasCechFour (fun s hs => capCechFive s ((FČ).monotone h45 hs)),
    cycle_class_nonzero hasCechFive capCechFive,
    inclusion_preserves_cycle_class hasAlphaFour hasAlphaFive ((Fα).monotone h45),
    inclusion_preserves_cycle_class hasCechFour hasCechFive ((FČ).monotone h45),
    inclusion_preserves_cycle_class hasAlphaFour hasCechFour (Alpha.labelledComplexFiltration_le_squaredCech _ 4),
    inclusion_preserves_cycle_class hasAlphaFive hasCechFive (Alpha.labelledComplexFiltration_le_squaredCech _ 5)⟩

/-- Coincident labels share an edge at zero, and the comparison commutes with the map
from the empty negative stage to that stage in every degree. -/
theorem coincidentLabels_crossZero (n : ℕ) :
    let p : Fin 2 → ℝ := fun _ => 0
    let e := alphaCechIso p ℚ n
    let step := homOfLE (by norm_num : (-1 : ℝ) ≤ 0)
    ({0, 1} : Finset (Fin 2)) ∈ Alpha.labelledComplex p 0 ∧
      (simplicialHomologyPModule ℚ (Alpha.labelledComplexFiltration p) n).map step ≫ e.hom.app 0 =
        e.hom.app (-1) ≫ (simplicialHomologyPModule ℚ (Alpha.squaredCechFiltration p) n).map step := by
  dsimp only
  constructor
  · exact (Alpha.mem_labelledComplex_iff _ _ _).2 ⟨by decide, 0, fun _ _ => by simp⟩
  · exact alphaCechIso_naturality _ _ _ (by norm_num)

example (p : Fin 0 → ℝ) (R : Type*) [Ring R] (n : ℕ) (t : ℝ) :
    IsIso ((inclusionHom R n (Alpha.labelledComplexFiltration_le_squaredCech p)).app t) :=
  isIso_alphaCechComparison_app p R n t

end
end TDA.Persistence.AlphaCechExamples
