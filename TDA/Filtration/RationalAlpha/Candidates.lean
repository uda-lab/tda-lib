import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.List.Dedup

set_option autoImplicit false

/-!
# Rational candidate centers for planar closed Voronoi cells

One list serves all faces. Each center records its squared distance to a nearest
site and the entire set of labels attaining that distance.
-/

namespace TDA.Filtration.RationalAlpha

abbrev Point := ℚ × ℚ

def sqDist (c p : Point) : ℚ := (c.1 - p.1)^2 + (c.2 - p.2)^2

def midpoint (p q : Point) : Point := ((p.1 + q.1)/2, (p.2 + q.2)/2)

/-- Normal of the bisector oriented from the first site to the second. -/
def normal (p q : Point) : Point := (q.1 - p.1, q.2 - p.2)

/-- Right-hand side of the bisector equation with the unscaled normal. -/
def offset (p q : Point) : ℚ := (q.1^2 + q.2^2 - (p.1^2 + p.2^2))/2

def det (u v : Point) : ℚ := u.1 * v.2 - u.2 * v.1

/-- Intersection of the two bisectors, when their normals are independent. -/
def circumcenter? (p q r : Point) : Option Point :=
  let u := normal p q
  let v := normal p r
  let d := det u v
  if d = 0 then none else
    some ((offset p q * v.2 - u.2 * offset p r)/d,
      (u.1 * offset p r - offset p q * v.1)/d)

variable {n : ℕ}

/-- Enumerate site, midpoint and noncollinear triple centers, removing duplicates. -/
def centers (p : Fin n → Point) : List Point :=
  let sites := (List.finRange n).map p
  (sites ++ sites.flatMap (fun a => sites.map (midpoint a)) ++
    sites.flatMap (fun a => sites.flatMap fun b => sites.filterMap (circumcenter? a b))).dedup

theorem mem_centers_iff (p : Fin n → Point) (c : Point) :
    c ∈ centers p ↔ (∃ i, p i = c) ∨ (∃ i j, midpoint (p i) (p j) = c) ∨
      ∃ i j k, circumcenter? (p i) (p j) (p k) = some c := by
  simp [centers, List.mem_flatMap, List.mem_filterMap, List.mem_map]

/-- A candidate center, its nearest squared distance, and all labels attaining it. -/
structure Record (n : ℕ) where
  center : Point
  grade : ℚ
  ties : Finset (Fin n)
  deriving DecidableEq

/-- A center has a nearest-site record exactly when there is at least one site. -/
def recordAt (p : Fin n → Point) (c : Point) : Option (Record n) :=
  ((List.finRange n).argmin fun i => sqDist c (p i)).map fun i =>
    let d := sqDist c (p i)
    ⟨c, d, Finset.univ.filter fun j => sqDist c (p j) = d⟩

def records (p : Fin n → Point) : List (Record n) := (centers p).filterMap (recordAt p)

/-- Choose a least squared grade among all full ties containing this nonempty face. -/
def lookup (rows : List (Record n)) (s : Finset (Fin n)) : Option (Record n) :=
  if s.Nonempty then (rows.filter fun r => s ⊆ r.ties).argmin Record.grade else none

/-- Return a minimum-grade witness, or `none` for an absent face. -/
def entry? (p : Fin n → Point) (s : Finset (Fin n)) : Option (Record n) :=
  lookup (records p) s

private theorem recordAt_spec {p : Fin n → Point} {c : Point} {r : Record n}
    (h : recordAt p c = some r) :
    r.center = c ∧ IsLeast (Set.range fun j => sqDist c (p j)) r.grade ∧
      ∀ j, j ∈ r.ties ↔ sqDist c (p j) = r.grade := by
  unfold recordAt at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨rfl, ⟨⟨i, rfl⟩, ?_⟩, by simp⟩
  rintro _ ⟨j, rfl⟩
  exact List.le_of_mem_argmin (List.mem_finRange j) hi

theorem record_spec {p : Fin n → Point} {r : Record n} (hr : r ∈ records p) :
    IsLeast (Set.range fun j => sqDist r.center (p j)) r.grade ∧
      ∀ j, j ∈ r.ties ↔ sqDist r.center (p j) = r.grade := by
  obtain ⟨c, _, h⟩ := List.mem_filterMap.mp hr
  obtain ⟨hc, hlow, ht⟩ := recordAt_spec h
  exact hc ▸ ⟨hlow, ht⟩

theorem exists_record {p : Fin n → Point} {c : Point} (hc : c ∈ centers p) (v : Fin n)
    (hv : ∀ j, sqDist c (p v) ≤ sqDist c (p j)) :
    ∃ r ∈ records p, r.center = c ∧ r.grade = sqDist c (p v) := by
  cases hi : (List.finRange n).argmin (fun i => sqDist c (p i)) with
  | none => exact False.elim (List.not_mem_nil (List.argmin_eq_none.mp hi ▸ List.mem_finRange v))
  | some i =>
    have he := le_antisymm (List.le_of_mem_argmin (List.mem_finRange v) hi) (hv i)
    let r : Record n := ⟨c, sqDist c (p i), Finset.univ.filter fun j =>
      sqDist c (p j) = sqDist c (p i)⟩
    exact ⟨r, List.mem_filterMap.mpr ⟨c, hc, by simp [recordAt, hi, r]⟩, rfl, he⟩

theorem lookup_spec {rows : List (Record n)} {s : Finset (Fin n)} {r : Record n}
    (h : lookup rows s = some r) :
    s.Nonempty ∧ r ∈ rows ∧ s ⊆ r.ties ∧ ∀ a ∈ rows, s ⊆ a.ties → r.grade ≤ a.grade := by
  unfold lookup at h
  split at h
  next hs =>
    obtain ⟨hr, ht⟩ := List.mem_filter.mp (List.argmin_mem h)
    exact ⟨hs, hr, of_decide_eq_true ht, fun a ha hsa =>
      List.le_of_mem_argmin (List.mem_filter.mpr ⟨ha, decide_eq_true hsa⟩) h⟩
  next => contradiction

theorem exists_lookup {rows : List (Record n)} {s : Finset (Fin n)} (hs : s.Nonempty)
    {a : Record n} (ha : a ∈ rows) (ht : s ⊆ a.ties) : ∃ r, lookup rows s = some r := by
  cases h : lookup rows s with
  | some r => exact ⟨r, rfl⟩
  | none =>
    simp only [lookup, ite_eq_left hs, List.argmin_eq_none] at h
    have hm : a ∈ rows.filter (fun r => decide (s ⊆ r.ties)) :=
      List.mem_filter.mpr ⟨ha, decide_eq_true ht⟩
    simp [h] at hm

end TDA.Filtration.RationalAlpha
