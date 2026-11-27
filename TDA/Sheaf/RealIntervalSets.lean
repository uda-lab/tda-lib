import TDA.Sheaf.RealConstructible
import Mathlib.Topology.LocallyClosed

/-!
# Strata, interval sets and stalks of interval sheaves on the real line

Fix strictly increasing breakpoints `p : Fin m → ℝ` (`hp : StrictMono p`) and write
`o = orient m` for the strata path of `TDA.Sheaf.RealStratification`, with vertices
`Fin (2 * m + 1)`.

* `stratum p v`: the points of the star of `v` that equal `p_i` whenever `v = 2i+1`. For an even
  vertex this is the open cell `star p v` (`stratum_of_even`), for the vertex `2i+1` it is the
  breakpoint `{p_i}` (`stratum_odd`; `stratum_odd_of_val` for a vertex `v` with
  `v.val = 2 * i.val + 1`). The strata are nonempty (`stratum_nonempty`), ordered
  like their vertices (`lt_of_mem_stratum`) and partition `ℝ` (`exists_mem_stratum`,
  `eq_of_mem_stratum`).
* `intervalSet p J`: the union of the strata of the vertices of an interval `J` of the strata
  path. `mem_intervalSet_iff_alive`: a point of the stratum `v` lies in `intervalSet p J` exactly
  when `v` lies in `J`. `intervalSet p J` is order-connected (`ordConnected_intervalSet`) and
  locally closed (`isLocallyClosed_intervalSet`); it is `ℝ`, a breakpoint, a single stratum,
  or an interval `[p_i, p_j]`, `[p_i, p_j)`, `(p_i, p_j]`, `(p_i, p_j)`, `(-∞, p_j)`,
  `(-∞, p_j]`, `(p_i, ∞)` or `[p_i, ∞)` according to the parities of its endpoints
  (`intervalSet_eq_univ`, `intervalSet_eq_singleton`, `intervalSet_eq_stratum`,
  `intervalSet_eq_Icc`, …, `intervalSet_eq_Ici`).
* Stalks: for a sheaf `F` constructible for the breakpoints of `p` and a point `x` of the
  stratum `v`, the germ `F(star p v) ⟶ F_x` is an isomorphism (`isIso_germ_star_of_mem_stratum`),
  so `(Φ M)_x ≅ M v` for `Φ = extension k hp` (`nonempty_stalk_extension_iso`).
* For an interval `J`, `Φ (interval J)` is the interval sheaf of `J`, with stalk `k` exactly on
  `intervalSet p J`: its stalk at `x` is isomorphic to `k` for `x ∈ intervalSet p J`
  (`nonempty_stalk_extension_interval_iso`) and zero otherwise
  (`isZero_stalk_extension_interval`); as dimensions, `1` on the interval set
  (`finrank_stalk_extension_interval_of_mem`) and `0` off it
  (`finrank_stalk_extension_interval_of_notMem`), and `finrank_stalk_extension_interval` states
  both as `if x ∈ intervalSet p J then 1 else 0` for an instance
  `[Decidable (x ∈ intervalSet p J)]`. The restriction from the star of a point to an adjacent
  cell, both in `J`, is an isomorphism (`isIso_extension_interval_map`, from
  `isIso_interval_map_gen` on the diagram side); through the germ isomorphisms it is the
  cospecialisation map between the stalks at the breakpoint and at a point of the cell.
-/

open CategoryTheory Limits TopologicalSpace Opposite TDA.Persistence
  TDA.Sheaf.AlternatingDiagram

namespace TDA.Sheaf.RealStratification

variable {m : ℕ} {p : Fin m → ℝ}

/-! ### Strata -/

/-- **The stratum of a vertex** `v` of the strata path: the points of the star of `v` that equal
`p_i` whenever `v = 2i+1`. It is the open cell `star p v` for an even vertex and the
breakpoint `{p_i}` for the vertex `2i+1`. -/
def stratum (p : Fin m → ℝ) (v : Fin (2 * m + 1)) : Set ℝ :=
  {x | x ∈ star p v ∧ ∀ i : Fin m, v.val = 2 * i.val + 1 → x = p i}

theorem mem_stratum {v : Fin (2 * m + 1)} {x : ℝ} :
    x ∈ stratum p v ↔ x ∈ star p v ∧ ∀ i : Fin m, v.val = 2 * i.val + 1 → x = p i :=
  Iff.rfl

theorem stratum_subset_star (v : Fin (2 * m + 1)) : stratum p v ⊆ star p v :=
  fun _ h => h.1

/-- The stratum of an even vertex is its open cell. -/
theorem stratum_of_even {v : Fin (2 * m + 1)} (hv : v.val % 2 = 0) :
    stratum p v = star p v := by
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, fun i hi => by omega⟩⟩

/-- The stratum of the vertex `2i+1` is the breakpoint `p_i`. -/
theorem stratum_odd (hp : StrictMono p) (i : Fin m) :
    stratum p ⟨2 * i.val + 1, by omega⟩ = {p i} := by
  ext x
  constructor
  · rintro ⟨-, h⟩
    exact h i rfl
  · rintro rfl
    refine ⟨apply_mem_star hp i, fun j hj => ?_⟩
    change 2 * i.val + 1 = 2 * j.val + 1 at hj
    rw [show j = i from Fin.ext (by omega)]

/-- The stratum of a vertex `v` with `v = 2i+1` is the breakpoint `p_i`. The vertex is free, so
`rw [stratum_odd_of_val hp i rfl]` rewrites the stratum at a literal vertex. -/
theorem stratum_odd_of_val (hp : StrictMono p) (i : Fin m) {v : Fin (2 * m + 1)}
    (hv : v.val = 2 * i.val + 1) : stratum p v = {p i} := by
  have h : v = ⟨2 * i.val + 1, by omega⟩ := Fin.ext hv
  rw [h]
  exact stratum_odd hp i

/-- Every stratum is nonempty. -/
theorem stratum_nonempty (hp : StrictMono p) (v : Fin (2 * m + 1)) : (stratum p v).Nonempty := by
  rcases Nat.even_or_odd' v.val with ⟨j, hj | hj⟩
  · obtain ⟨x, hx⟩ := (isBasicOpen_star hp v).1
    exact ⟨x, hx, fun i hi => by omega⟩
  · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j := ⟨⟨j, by have := v.isLt; omega⟩, rfl⟩
    refine ⟨p i, (apply_mem_star_iff hp i).2 (by omega), fun i' hi' => ?_⟩
    rw [show i' = i from Fin.ext (by omega)]

/-- **Strata are ordered like their vertices**: a point of the stratum `v` lies below every
point of the stratum `u` when `v < u`. -/
theorem lt_of_mem_stratum {v u : Fin (2 * m + 1)} {x y : ℝ}
    (hx : x ∈ stratum p v) (hy : y ∈ stratum p u) (h : v < u) : x < y := by
  have h' := Fin.lt_def.1 h
  rcases Nat.even_or_odd' u.val with ⟨j, hj | hj⟩
  · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j - 1 := ⟨⟨j - 1, by have := u.isLt; omega⟩, rfl⟩
    have h1 : p i < y := (hy.1 i).1 (by omega)
    rcases (show v.val < 2 * i.val + 1 ∨ v.val = 2 * i.val + 1 by omega) with h2 | h2
    · exact ((hx.1 i).2 h2).trans h1
    · rw [hx.2 i h2]
      exact h1
  · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j := ⟨⟨j, by have := u.isLt; omega⟩, rfl⟩
    rw [hy.2 i (by omega)]
    exact (hx.1 i).2 (by omega)

/-- Distinct strata are disjoint. -/
theorem eq_of_mem_stratum {v u : Fin (2 * m + 1)} {x : ℝ}
    (hv : x ∈ stratum p v) (hu : x ∈ stratum p u) : v = u := by
  rcases lt_trichotomy v u with h | h | h
  · exact absurd (lt_of_mem_stratum hv hu h) (lt_irrefl x)
  · exact h
  · exact absurd (lt_of_mem_stratum hu hv h) (lt_irrefl x)

/-- **The strata cover the real line**: every point lies in a stratum. -/
theorem exists_mem_stratum (hp : StrictMono p) (x : ℝ) : ∃ v, x ∈ stratum p v := by
  have hO : IsOpen ((↑(breakpoints p) \ {x} : Set ℝ)ᶜ) :=
    (((breakpoints p).finite_toSet.subset Set.sdiff_subset).isClosed).isOpen_compl
  obtain ⟨T, hT, hxT, hTO⟩ := Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen (breakpoints p))
    (show x ∈ (⟨_, hO⟩ : Opens realLine) from fun h => h.2 rfl)
  refine ⟨tau p ⟨T, hT⟩, le_star_tau hp ⟨T, hT⟩ hxT, fun i hi => ?_⟩
  have hpi : p i ∈ ((⟨T, hT⟩ : Basic (breakpoints p)).1 : Set ℝ) ∩ ↑(breakpoints p) :=
    star_tau_inter hp ⟨T, hT⟩ ▸ ⟨(apply_mem_star_iff hp i).2 hi, apply_mem_breakpoints p i⟩
  by_contra hne
  exact hTO hpi.1 ⟨hpi.2, fun h => hne h.symm⟩

/-- The star of the stratum of `x` meets the breakpoints at most in `x`. -/
theorem eq_of_mem_star_inter_breakpoints (hp : StrictMono p) {v : Fin (2 * m + 1)} {x y : ℝ}
    (hx : x ∈ stratum p v) (hy : y ∈ (star p v : Set ℝ) ∩ ↑(breakpoints p)) : y = x := by
  obtain ⟨i, rfl⟩ := mem_breakpoints.1 hy.2
  exact (hx.2 i ((apply_mem_star_iff hp i).1 hy.1)).symm

/-! ### Interval sets -/

/-- **The interval set** of an interval `J` of the strata path: the union of the strata of the
vertices of `J`, a subset of the real line. -/
def intervalSet (p : Fin m → ℝ) (J : FiniteInterval (2 * m + 1)) : Set ℝ :=
  ⋃ (v : Fin (2 * m + 1)) (_ : J.alive v), stratum p v

theorem mem_intervalSet {J : FiniteInterval (2 * m + 1)} {x : ℝ} :
    x ∈ intervalSet p J ↔ ∃ v, J.alive v ∧ x ∈ stratum p v := by
  simp only [intervalSet, Set.mem_iUnion, exists_prop]

theorem stratum_subset_intervalSet {J : FiniteInterval (2 * m + 1)} {v : Fin (2 * m + 1)}
    (hv : J.alive v) : stratum p v ⊆ intervalSet p J :=
  fun _ hx => mem_intervalSet.2 ⟨v, hv, hx⟩

/-- A point of the stratum `v` lies in `intervalSet p J` exactly when `v` lies in `J`. -/
theorem mem_intervalSet_iff_alive {J : FiniteInterval (2 * m + 1)}
    {v : Fin (2 * m + 1)} {x : ℝ} (hx : x ∈ stratum p v) : x ∈ intervalSet p J ↔ J.alive v := by
  rw [mem_intervalSet]
  exact ⟨fun ⟨u, hu, hxu⟩ => eq_of_mem_stratum hxu hx ▸ hu, fun hv => ⟨v, hv, hx⟩⟩

/-- The constraints of the lower end of an interval starting at the vertex `b`. -/
private def lowerSet (p : Fin m → ℝ) (b : ℕ) : Set ℝ :=
  {x | ∀ i : Fin m, (2 * i.val + 1 < b → p i < x) ∧ (2 * i.val + 1 = b → p i ≤ x)}

/-- The constraints of the upper end of an interval ending before the vertex `d`. -/
private def upperSet (p : Fin m → ℝ) (d : ℕ) : Set ℝ :=
  {x | ∀ i : Fin m, (d ≤ 2 * i.val + 1 → x < p i) ∧ (2 * i.val + 2 = d → x ≤ p i)}

private theorem intervalSet_eq_inter (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    intervalSet p J = lowerSet p J.birth ∩ upperSet p J.death := by
  have hbd := J.birth_lt_death
  have hdm := J.death_le_size
  ext x
  rw [mem_intervalSet]
  constructor
  · rintro ⟨v, ⟨hb, hd⟩, hx⟩
    refine ⟨fun i => ⟨fun h => (hx.1 i).1 (by omega), fun h => ?_⟩,
      fun i => ⟨fun h => (hx.1 i).2 (by omega), fun h => ?_⟩⟩
    · rcases (show 2 * i.val + 1 < v.val ∨ v.val = 2 * i.val + 1 by omega) with h' | h'
      · exact ((hx.1 i).1 h').le
      · exact (hx.2 i h').ge
    · rcases (show v.val < 2 * i.val + 1 ∨ v.val = 2 * i.val + 1 by omega) with h' | h'
      · exact ((hx.1 i).2 h').le
      · exact (hx.2 i h').le
  · rintro ⟨hl, hu⟩
    obtain ⟨v, hx⟩ := exists_mem_stratum hp x
    refine ⟨v, ⟨?_, ?_⟩, hx⟩
    · by_contra hlt
      have hlt := not_le.1 hlt
      rcases Nat.even_or_odd' v.val with ⟨j, hj | hj⟩
      · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j := ⟨⟨j, by omega⟩, rfl⟩
        have h1 : x < p i := (hx.1 i).2 (by omega)
        rcases (show 2 * i.val + 1 < J.birth ∨ 2 * i.val + 1 = J.birth by omega) with h2 | h2
        · exact absurd ((hl i).1 h2) (not_lt.2 h1.le)
        · exact absurd ((hl i).2 h2) (not_le.2 h1)
      · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j := ⟨⟨j, by omega⟩, rfl⟩
        have h1 : x = p i := hx.2 i (by omega)
        exact absurd ((hl i).1 (by omega)) (by rw [h1]; exact lt_irrefl _)
    · by_contra hge
      have hge := not_lt.1 hge
      rcases Nat.even_or_odd' v.val with ⟨j, hj | hj⟩
      · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j - 1 :=
          ⟨⟨j - 1, by have := v.isLt; omega⟩, rfl⟩
        have h1 : p i < x := (hx.1 i).1 (by omega)
        rcases (show J.death ≤ 2 * i.val + 1 ∨ 2 * i.val + 2 = J.death by omega) with h2 | h2
        · exact absurd ((hu i).1 h2) (not_lt.2 h1.le)
        · exact absurd ((hu i).2 h2) (not_le.2 h1)
      · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j := ⟨⟨j, by have := v.isLt; omega⟩, rfl⟩
        have h1 : x = p i := hx.2 i (by omega)
        exact absurd ((hu i).1 (by omega)) (by rw [h1]; exact lt_irrefl _)

private theorem lowerSet_zero : lowerSet p 0 = Set.univ :=
  Set.eq_univ_of_forall fun _ _ => ⟨fun h => by omega, fun h => by omega⟩

private theorem lowerSet_odd (hp : StrictMono p) (i : Fin m) :
    lowerSet p (2 * i.val + 1) = Set.Ici (p i) := by
  ext x
  refine ⟨fun h => (h i).2 rfl, fun h j => ⟨fun hj => (hp (Fin.lt_def.2 (by omega))).trans_le h,
    fun hj => ?_⟩⟩
  rw [show j = i from Fin.ext (by omega)]
  exact h

private theorem lowerSet_even (hp : StrictMono p) (i : Fin m) :
    lowerSet p (2 * i.val + 2) = Set.Ioi (p i) := by
  ext x
  exact ⟨fun h => (h i).1 (by omega), fun h j =>
    ⟨fun hj => (hp.monotone (Fin.le_def.2 (by omega))).trans_lt h, fun hj => by omega⟩⟩

private theorem upperSet_top : upperSet p (2 * m + 1) = Set.univ :=
  Set.eq_univ_of_forall fun _ i => ⟨fun h => by omega, fun h => by omega⟩

private theorem upperSet_odd (hp : StrictMono p) (j : Fin m) :
    upperSet p (2 * j.val + 1) = Set.Iio (p j) := by
  ext x
  exact ⟨fun h => (h j).1 le_rfl, fun h i =>
    ⟨fun hi => h.trans_le (hp.monotone (Fin.le_def.2 (by omega))), fun hi => by omega⟩⟩

private theorem upperSet_even (hp : StrictMono p) (j : Fin m) :
    upperSet p (2 * j.val + 2) = Set.Iic (p j) := by
  ext x
  refine ⟨fun h => (h j).2 rfl, fun h i =>
    ⟨fun hi => h.trans_lt (hp (Fin.lt_def.2 (by omega))), fun hi => ?_⟩⟩
  rw [show i = j from Fin.ext (by omega)]
  exact h

/-- A property of subsets of `ℝ` that holds for `ℝ` and the closed and open right half-lines holds
for the lower constraints of every interval of the strata path. -/
private theorem lowerSet_induction (hp : StrictMono p) {b : ℕ} (hb : b ≤ 2 * m)
    (P : Set ℝ → Prop) (h₀ : P Set.univ) (h₁ : ∀ a, P (Set.Ici a)) (h₂ : ∀ a, P (Set.Ioi a)) :
    P (lowerSet p b) := by
  rcases Nat.even_or_odd' b with ⟨j, hj | hj⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hj, Nat.mul_zero, lowerSet_zero]
      exact h₀
    · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j - 1 := ⟨⟨j - 1, by omega⟩, rfl⟩
      rw [show b = 2 * i.val + 2 by omega, lowerSet_even hp]
      exact h₂ _
  · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j := ⟨⟨j, by omega⟩, rfl⟩
    rw [show b = 2 * i.val + 1 by omega, lowerSet_odd hp]
    exact h₁ _

/-- A property of subsets of `ℝ` that holds for `ℝ` and the open and closed left half-lines holds
for the upper constraints of every interval of the strata path. -/
private theorem upperSet_induction (hp : StrictMono p) {d : ℕ} (hd₀ : 1 ≤ d) (hd : d ≤ 2 * m + 1)
    (P : Set ℝ → Prop) (h₀ : P Set.univ) (h₁ : ∀ a, P (Set.Iio a)) (h₂ : ∀ a, P (Set.Iic a)) :
    P (upperSet p d) := by
  rcases Nat.even_or_odd' d with ⟨j, hj | hj⟩
  · obtain ⟨i, hi⟩ : ∃ i : Fin m, i.val = j - 1 := ⟨⟨j - 1, by omega⟩, rfl⟩
    rw [show d = 2 * i.val + 2 by omega, upperSet_even hp]
    exact h₂ _
  · rcases (show j = m ∨ j < m by omega) with rfl | hjm
    · rw [hj, upperSet_top]
      exact h₀
    · rw [hj, show j = (⟨j, hjm⟩ : Fin m).val from rfl, upperSet_odd hp]
      exact h₁ _

/-- **Interval sets are intervals**: `intervalSet p J` is order-connected. -/
theorem ordConnected_intervalSet (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    (intervalSet p J).OrdConnected := by
  have hbd := J.birth_lt_death
  have hdm := J.death_le_size
  rw [intervalSet_eq_inter hp]
  exact (lowerSet_induction hp (by omega) Set.OrdConnected Set.ordConnected_univ
    (fun _ => Set.ordConnected_Ici) fun _ => Set.ordConnected_Ioi).inter
    (upperSet_induction hp (by omega) hdm Set.OrdConnected Set.ordConnected_univ
      (fun _ => Set.ordConnected_Iio) fun _ => Set.ordConnected_Iic)

/-- **Interval sets are locally closed**: `intervalSet p J` is the intersection of an open and a
closed subset of `ℝ`. -/
theorem isLocallyClosed_intervalSet (hp : StrictMono p) (J : FiniteInterval (2 * m + 1)) :
    IsLocallyClosed (intervalSet p J) := by
  have hbd := J.birth_lt_death
  have hdm := J.death_le_size
  rw [intervalSet_eq_inter hp]
  exact (lowerSet_induction hp (by omega) IsLocallyClosed isOpen_univ.isLocallyClosed
    (fun _ => isClosed_Ici.isLocallyClosed) fun _ => isOpen_Ioi.isLocallyClosed).inter
    (upperSet_induction hp (by omega) hdm IsLocallyClosed isOpen_univ.isLocallyClosed
      (fun _ => isOpen_Iio.isLocallyClosed) fun _ => isClosed_Iic.isLocallyClosed)

/-! ### Explicit interval sets -/

/-- The interval of all vertices has the whole line as interval set. -/
theorem intervalSet_eq_univ (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)}
    (hb : J.birth = 0) (hd : J.death = 2 * m + 1) : intervalSet p J = Set.univ := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_zero, upperSet_top, Set.univ_inter]

/-- The interval of one vertex has its stratum as interval set. -/
theorem intervalSet_eq_stratum {J : FiniteInterval (2 * m + 1)}
    {v : Fin (2 * m + 1)} (hb : J.birth = v.val) (hd : J.death = v.val + 1) :
    intervalSet p J = stratum p v := by
  ext x
  rw [mem_intervalSet]
  refine ⟨fun ⟨u, hu, hx⟩ => ?_, fun hx => ⟨v, ⟨by omega, by omega⟩, hx⟩⟩
  rw [show v = u from Fin.ext (by have := hu.1; have := hu.2; omega)]
  exact hx

/-- The interval of the vertex `2i+1` has the breakpoint `p_i` as interval set. -/
theorem intervalSet_eq_singleton (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)}
    {i : Fin m} (hb : J.birth = 2 * i.val + 1) (hd : J.death = 2 * i.val + 2) :
    intervalSet p J = {p i} := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_odd hp, upperSet_even hp, Set.Ici_inter_Iic,
    Set.Icc_self]

/-- The interval from the vertex `2i+1` to the vertex `2j+1` has interval set `[p_i, p_j]`. -/
theorem intervalSet_eq_Icc (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {i j : Fin m}
    (hb : J.birth = 2 * i.val + 1) (hd : J.death = 2 * j.val + 2) :
    intervalSet p J = Set.Icc (p i) (p j) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_odd hp, upperSet_even hp, Set.Ici_inter_Iic]

/-- The interval from the vertex `2i+1` to the vertex `2j` has interval set `[p_i, p_j)`. -/
theorem intervalSet_eq_Ico (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {i j : Fin m}
    (hb : J.birth = 2 * i.val + 1) (hd : J.death = 2 * j.val + 1) :
    intervalSet p J = Set.Ico (p i) (p j) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_odd hp, upperSet_odd hp, Set.Ici_inter_Iio]

/-- The interval from the vertex `2i+2` to the vertex `2j+1` has interval set `(p_i, p_j]`. -/
theorem intervalSet_eq_Ioc (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {i j : Fin m}
    (hb : J.birth = 2 * i.val + 2) (hd : J.death = 2 * j.val + 2) :
    intervalSet p J = Set.Ioc (p i) (p j) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_even hp, upperSet_even hp, Set.Ioi_inter_Iic]

/-- The interval from the vertex `2i+2` to the vertex `2j` has interval set `(p_i, p_j)`. -/
theorem intervalSet_eq_Ioo (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {i j : Fin m}
    (hb : J.birth = 2 * i.val + 2) (hd : J.death = 2 * j.val + 1) :
    intervalSet p J = Set.Ioo (p i) (p j) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_even hp, upperSet_odd hp, Set.Ioi_inter_Iio]

/-- The interval from the vertex `0` to the vertex `2j` has interval set `(-∞, p_j)`. -/
theorem intervalSet_eq_Iio (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {j : Fin m}
    (hb : J.birth = 0) (hd : J.death = 2 * j.val + 1) :
    intervalSet p J = Set.Iio (p j) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_zero, upperSet_odd hp, Set.univ_inter]

/-- The interval from the vertex `0` to the vertex `2j+1` has interval set `(-∞, p_j]`. -/
theorem intervalSet_eq_Iic (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {j : Fin m}
    (hb : J.birth = 0) (hd : J.death = 2 * j.val + 2) :
    intervalSet p J = Set.Iic (p j) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_zero, upperSet_even hp, Set.univ_inter]

/-- The interval from the vertex `2i+2` to the last vertex has interval set `(p_i, ∞)`. -/
theorem intervalSet_eq_Ioi (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {i : Fin m}
    (hb : J.birth = 2 * i.val + 2) (hd : J.death = 2 * m + 1) :
    intervalSet p J = Set.Ioi (p i) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_even hp, upperSet_top, Set.inter_univ]

/-- The interval from the vertex `2i+1` to the last vertex has interval set `[p_i, ∞)`. -/
theorem intervalSet_eq_Ici (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)} {i : Fin m}
    (hb : J.birth = 2 * i.val + 1) (hd : J.death = 2 * m + 1) :
    intervalSet p J = Set.Ici (p i) := by
  rw [intervalSet_eq_inter hp, hb, hd, lowerSet_odd hp, upperSet_top, Set.inter_univ]

end TDA.Sheaf.RealStratification

namespace TDA.Sheaf.AlternatingDiagram

/-- The transition map of an interval diagram between two vertices of the interval is an
isomorphism. -/
theorem isIso_interval_map_gen {k : Type*} [Field k] {n : ℕ} {o : Fin n → Bool}
    (J : FiniteInterval (n + 1))
    {v w : Fin (n + 1)} (h : Arrow o v w) (hv : J.alive v) (hw : J.alive w) :
    IsIso ((interval (k := k) o J).map (gen h)) := by
  rw [interval, ofArrows_map_gen]
  have hb : Function.Bijective (fiberMap (k := k) J v w) := by
    refine ⟨fun a b hab => Subtype.ext ?_, fun y => ⟨⟨(y : k), by
      simp [FiniteInterval.fiber, hv]⟩, Subtype.ext ?_⟩⟩
    · have := congrArg Subtype.val hab
      simpa [fiberMap_val, hv, hw] using this
    · simp [fiberMap_val, hv, hw]
  exact (LinearEquiv.ofBijective _ hb).toModuleIso.isIso_hom

end TDA.Sheaf.AlternatingDiagram

namespace TDA.Sheaf.RealConstructible

open TDA.Sheaf.RealStratification

variable {m : ℕ} {p : Fin m → ℝ}

/-! ### Stalks -/

/-- **Stalks of constructible sheaves.** For a sheaf `F` constructible for the breakpoints of
`p` and a point `x` of the stratum `v`, the germ `F(star p v) ⟶ F_x` is an isomorphism. -/
theorem isIso_germ_star_of_mem_stratum {k : Type} [DivisionRing k] (hp : StrictMono p)
    {F : TopCat.Sheaf (ModuleCat.{0} k) realLine} (hF : IsConstructible (breakpoints p) F)
    {v : Fin (2 * m + 1)} {x : ℝ} (hx : x ∈ stratum p v) :
    IsIso (F.presheaf.germ (star p v) x (stratum_subset_star v hx)) :=
  isIso_germ_of_isConstructible hF (isBasicOpen_star hp v) _
    fun _ hy => eq_of_mem_star_inter_breakpoints hp hx hy

variable (k : Type) [Field k]

/-- The stalk of `Φ M` at a point of the stratum `v` is `M v`, for a diagram `M` with
finite-dimensional values. -/
theorem nonempty_stalk_extension_iso (hp : StrictMono p) {M : Diagram k (orient m)}
    (hM : ∀ X, FiniteDimensional k (M.obj X)) {v : Fin (2 * m + 1)} {x : ℝ}
    (hx : x ∈ stratum p v) :
    Nonempty (((extension k hp).obj M).presheaf.stalk x ≅ M.obj (vtx (orient m) v)) := by
  have := isIso_germ_star_of_mem_stratum hp (isConstructible_extension k hp hM) hx
  exact ⟨(asIso (((extension k hp).obj M).presheaf.germ (star p v) x
    (stratum_subset_star v hx))).symm ≪≫ extensionStarIso k hp M v⟩

/-- **Stalks of interval sheaves, on the interval.** `Φ (interval J)` is the interval sheaf of
`J`, with stalk `k` exactly on `intervalSet p J`: at a point of `intervalSet p J` its stalk is
isomorphic to `k`. -/
theorem nonempty_stalk_extension_interval_iso (hp : StrictMono p)
    {J : FiniteInterval (2 * m + 1)} {x : ℝ} (hx : x ∈ intervalSet p J) :
    Nonempty (((extension k hp).obj (interval (orient m) J)).presheaf.stalk x ≅
      ModuleCat.of k k) := by
  obtain ⟨v, hv, hxv⟩ := mem_intervalSet.1 hx
  obtain ⟨e⟩ := nonempty_stalk_extension_iso k hp (M := interval (orient m) J)
    (fun _ => inferInstance) hxv
  exact ⟨e ≪≫ (LinearEquiv.ofTop (J.fiber (k := k) v)
    (by simp [FiniteInterval.fiber, hv])).toModuleIso⟩

/-- **Stalks of interval sheaves, off the interval.** The stalk of the interval sheaf
`Φ (interval J)` at a point outside `intervalSet p J` is zero. -/
theorem isZero_stalk_extension_interval (hp : StrictMono p) {J : FiniteInterval (2 * m + 1)}
    {x : ℝ} (hx : x ∉ intervalSet p J) :
    IsZero (((extension k hp).obj (interval (orient m) J)).presheaf.stalk x) := by
  obtain ⟨v, hxv⟩ := exists_mem_stratum hp x
  obtain ⟨e⟩ := nonempty_stalk_extension_iso k hp (M := interval (orient m) J)
    (fun _ => inferInstance) hxv
  have hv : ¬J.alive v := fun hv => hx ((mem_intervalSet_iff_alive hxv).2 hv)
  have : Subsingleton ((interval (k := k) (orient m) J).obj (vtx (orient m) v)) :=
    ⟨fun a b => Subtype.ext ((fiber_val_eq_zero hv a).trans (fiber_val_eq_zero hv b).symm)⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso e

/-- **The stalk dimension of an interval sheaf on the interval set.** The stalk of the interval
sheaf `Φ (interval J)` at a point of `intervalSet p J` has dimension one. -/
theorem finrank_stalk_extension_interval_of_mem (hp : StrictMono p)
    {J : FiniteInterval (2 * m + 1)} {x : ℝ} (hx : x ∈ intervalSet p J) :
    Module.finrank k (((extension k hp).obj (interval (orient m) J)).presheaf.stalk x) = 1 := by
  obtain ⟨e⟩ := nonempty_stalk_extension_interval_iso k hp hx
  rw [e.toLinearEquiv.finrank_eq]
  exact Module.finrank_self k

/-- **The stalk dimension of an interval sheaf off the interval set.** The stalk of the interval
sheaf `Φ (interval J)` at a point outside `intervalSet p J` has dimension zero. -/
theorem finrank_stalk_extension_interval_of_notMem (hp : StrictMono p)
    {J : FiniteInterval (2 * m + 1)} {x : ℝ} (hx : x ∉ intervalSet p J) :
    Module.finrank k (((extension k hp).obj (interval (orient m) J)).presheaf.stalk x) = 0 := by
  have := ModuleCat.isZero_iff_subsingleton.1 (isZero_stalk_extension_interval k hp hx)
  exact Module.finrank_zero_of_subsingleton

/-- **The stalk dimension of an interval sheaf.** The stalk of the interval sheaf
`Φ (interval J)` at `x` has dimension one when `x ∈ intervalSet p J` and zero otherwise. The
decidability of `x ∈ intervalSet p J` is an instance argument: any instance gives the same
value of the `if`. `finrank_stalk_extension_interval_of_mem` and
`finrank_stalk_extension_interval_of_notMem` state the two cases without an instance. -/
theorem finrank_stalk_extension_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    (x : ℝ) [Decidable (x ∈ intervalSet p J)] :
    Module.finrank k (((extension k hp).obj (interval (orient m) J)).presheaf.stalk x) =
      if x ∈ intervalSet p J then 1 else 0 := by
  split_ifs with hx
  · exact finrank_stalk_extension_interval_of_mem k hp hx
  · exact finrank_stalk_extension_interval_of_notMem k hp hx

/-- **Restrictions of interval sheaves inside the interval.** For an arrow from the point `v` to
an adjacent cell `w`, both in `J`, the restriction of the interval sheaf `Φ (interval J)` from
the star of `v` to the star of `w` is an isomorphism. Through the germ isomorphisms of
`isIso_germ_star_of_mem_stratum` it is the cospecialisation map from the stalk at the breakpoint
to the stalk at a point of the cell. -/
theorem isIso_extension_interval_map (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {v w : Fin (2 * m + 1)} (h : Arrow (orient m) v w) (hv : J.alive v) (hw : J.alive w) :
    IsIso (((extension k hp).obj (interval (orient m) J)).presheaf.map
      (homOfLE (star_le_star_of_arrow p h)).op) := by
  let e := (extensionSectionsIso k hp).app (interval (orient m) J)
  have := isIso_interval_map_gen (k := k) J h hv hw
  have hn := e.hom.naturality (gen h)
  rw [← sections_map_gen k p _ h]
  have : ((sections k p).obj ((extension k hp).obj (interval (orient m) J))).map (gen h) =
      e.hom.app _ ≫ (interval (orient m) J).map (gen h) ≫ e.inv.app _ := by
    rw [← reassoc_of% hn]
    simp
  rw [this]
  exact IsIso.comp_isIso' (e.app _).isIso_hom (IsIso.comp_isIso' inferInstance (e.app _).isIso_inv)

end TDA.Sheaf.RealConstructible
