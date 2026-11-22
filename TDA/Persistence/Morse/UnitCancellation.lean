import TDA.Persistence.Reduction.FiniteInput

/-!
# Cancelling one equal-grade unit pair of a filtered based complex

A based complex is a finite index type `ι` of basis generators with a matrix
`D : Matrix ι ι k` over a commutative ring `k`. Column `c` is `d c`, so `D r c` is the
coefficient of `r` in `d c` and matrix product is composition; this is the column convention
of `FiniteInput.boundary`. `IsBasedDifferential degree D` asks for `D * D = 0` and for
`D r c ≠ 0 → degree c = degree r + 1`; `IsFilteredDifferential` adds that `D` does not
increase an integer grade (`GradeNonincreasing grade grade D`). No ordering of the basis and
no triangularity is assumed.

A unit pair (`IsUnitPair D a b`) is `a ≠ b` with `D a b = 1`. The survivors
`PairSurvivor a b` are the generators other than `a` and `b`, kept as a subtype of `ι` with
their original IDs. With `H a = b` (`homotopy`), the coordinate restriction `Q`
(`survivorProjection`) and inclusion `J` (`survivorInclusion`), the reduced differential,
projection and inclusion are given by computable entry formulas:

* `reducedDifferential D a b r s = D r s - D r b * D a s`;
* `projection D a b s x = δ(s, x) - [x = a] D s b`;
* `inclusion D a b x s = δ(x, s) - [x = b] D a s`.

`reducedDifferential_eq`, `projection_eq` and `inclusion_eq` identify them with the product
forms `Q (D - D H D) J`, `Q (1 - D H)` and `(1 - H D) J`, for every `D`.

Under `D * D = 0` and `IsUnitPair D a b`, the contraction identities are
`reducedDifferential_sq_zero`, the chain-map equations `projection_mul` and `mul_inclusion`,
and `one_sub_inclusion_mul_projection` (`1 - i p = D H + H D`). `projection_mul_inclusion`
(`p i = 1`) and the annihilation identities `H H = 0`, `p H = 0`, `H i = 0` need only
`a ≠ b`. The degree theorems add `IsBasedDifferential`. The filtration theorems assume that
`D` is grade-nonincreasing and that `grade a = grade b`; then `d'`, `p`, `i` and `H` are all
grade-nonincreasing, and by `GradeNonincreasing.mulVec_sublevelSupported` each maps vectors
supported in grades `≤ t` to such vectors.

## Source and convention digest

Mischaikow and Nanda, *Morse Theory for Filtrations and Efficient Computation of Persistent
Homology*, Discrete Comput. Geom. 50 (2013), DOI 10.1007/s00454-013-9529-6 (register card
`MN13` in `docs/math/references.md`). The reduction step of the proof of Thm. 2.4, eqs.
(8)–(10) and Lemma 2.5, is specialised here to a single pair with unit coefficient
`κ(w(Q), Q) = 1`, where MN's `κ(η, ξ)`, the coefficient of `ξ` in `∂η`, is `D ξ η`, with
`Q = a` and `w(Q) = b`. MN work over a principal ideal domain inside an acyclic matching;
these statements hold over any commutative ring and need no acyclicity. The filtration
statements specialise the argument of Prop. 4.4 to one pair, with an integer grade in place of
MN's frame index. No iteration, homology or persistence isomorphism is stated here, and no
rescaling by a general unit is provided.
-/

set_option autoImplicit false

namespace TDA.Persistence.Morse.Cancellation

open TDA.Persistence.Reduction

section Grades

variable {κ μ ν : Type*} {k : Type*}

/-- Row grade at most column grade on the support (column `c` is the image of basis `c`). -/
def GradeNonincreasing [Zero k] (gr : κ → ℤ) (gc : μ → ℤ) (M : Matrix κ μ k) : Prop :=
  ∀ r c, M r c ≠ 0 → gr r ≤ gc c

/-- Grade nonincreasingness of a finite matrix with decidable entries is decidable. -/
instance GradeNonincreasing.decidable [Zero k] [DecidableEq k] [Fintype κ] [Fintype μ]
    (gr : κ → ℤ) (gc : μ → ℤ)
    (M : Matrix κ μ k) : Decidable (GradeNonincreasing gr gc M) :=
  @Fintype.decidableForallFintype _ _
    (fun _ => @Fintype.decidableForallFintype _ _ (fun _ => inferInstance) _) _

/-- A coordinate vector vanishes above grade `t`. -/
def SublevelSupported [Zero k] (g : κ → ℤ) (t : ℤ) (x : κ → k) : Prop :=
  ∀ c, t < g c → x c = 0

/-- A grade-nonincreasing matrix maps vectors supported in grades `≤ t` to such vectors. -/
theorem GradeNonincreasing.mulVec_sublevelSupported [CommRing k] [Fintype μ]
    {gr : κ → ℤ} {gc : μ → ℤ} {M : Matrix κ μ k} (hM : GradeNonincreasing gr gc M)
    {t : ℤ} {x : μ → k} (hx : SublevelSupported gc t x) :
    SublevelSupported gr t (M.mulVec x) := by
  intro r hr
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : M r c = 0
  · simp [h]
  · rw [hx c (lt_of_lt_of_le hr (hM r c h)), mul_zero]

/-- Grade-nonincreasing matrices compose. -/
theorem GradeNonincreasing.mul [CommRing k] [Fintype μ] {gr : κ → ℤ} {gm : μ → ℤ}
    {gc : ν → ℤ} {M : Matrix κ μ k} {N : Matrix μ ν k}
    (hM : GradeNonincreasing gr gm M) (hN : GradeNonincreasing gm gc N) :
    GradeNonincreasing gr gc (M * N) := by
  intro r c h
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (hM r m (left_ne_zero_of_mul hm)).trans (hN m c (right_ne_zero_of_mul hm))

end Grades

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [CommRing k]

/-- A square-zero differential lowering homological degree by one. -/
structure IsBasedDifferential (degree : ι → ℕ) (D : Matrix ι ι k) : Prop where
  sq_zero : D * D = 0
  lowers_degree : ∀ r c, D r c ≠ 0 → degree c = degree r + 1

/-- A based differential that does not increase grades. -/
structure IsFilteredDifferential (degree : ι → ℕ) (grade : ι → ℤ) (D : Matrix ι ι k) : Prop
    extends IsBasedDifferential degree D where
  grade_le : GradeNonincreasing grade grade D

/-- `a` is a face of `b` with coefficient one. -/
structure IsUnitPair (D : Matrix ι ι k) (a b : ι) : Prop where
  ne : a ≠ b
  coeff : D a b = 1

/-- The basis generators other than `a` and `b`. -/
abbrev PairSurvivor (a b : ι) := {x : ι // x ≠ a ∧ x ≠ b}

/-- Removing two distinct generators leaves `card ι - 2` survivors. -/
theorem card_pairSurvivor {a b : ι} (hne : a ≠ b) :
    Fintype.card (PairSurvivor a b) = Fintype.card ι - 2 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : ι => x ≠ a ∧ x ≠ b) = Finset.univ \ {a, b} := by
    ext x; simp [not_or]
  rw [this, Finset.card_univ_sdiff, Finset.card_pair hne]

/-- `Q`: restriction of coordinates to the survivors. -/
def survivorProjection (a b : ι) : Matrix (PairSurvivor a b) ι k :=
  fun s x => if s.val = x then 1 else 0

/-- `J`: the survivor coordinate inclusion. -/
def survivorInclusion (a b : ι) : Matrix ι (PairSurvivor a b) k :=
  fun x s => if x = s.val then 1 else 0

/-- `H a = b`, zero on every other generator. -/
def homotopy (a b : ι) : Matrix ι ι k :=
  fun x y => if x = b ∧ y = a then 1 else 0

/-- `d'[r,s] = D[r,s] - D[r,b] D[a,s]`. -/
def reducedDifferential (D : Matrix ι ι k) (a b : ι) :
    Matrix (PairSurvivor a b) (PairSurvivor a b) k :=
  fun r s => D r s - D r b * D a s

/-- `p = Q (1 - D H)`: `p s = s`, `p a = -(Q (d b))`, `p b = 0`. -/
def projection (D : Matrix ι ι k) (a b : ι) : Matrix (PairSurvivor a b) ι k :=
  fun s x => (if s.val = x then 1 else 0) - (if x = a then D s b else 0)

/-- `i = (1 - H D) J`: `i s = s - D[a,s] b`. -/
def inclusion (D : Matrix ι ι k) (a b : ι) : Matrix ι (PairSurvivor a b) k :=
  fun x s => (if x = s.val then 1 else 0) - (if x = b then D a s else 0)

/-! ## Entry lemmas -/

section Entries

variable {a b : ι}

/-- A sum over the survivors is the full sum minus the two removed terms. -/
private theorem sum_pairSurvivor (hne : a ≠ b) (f : ι → k) :
    ∑ s : PairSurvivor a b, f s.val = ∑ x, f x - f a - f b := by
  have h1 : ∑ s : PairSurvivor a b, f s.val =
      ∑ x ∈ Finset.univ.filter (fun x : ι => x ≠ a ∧ x ≠ b), f x :=
    (Finset.sum_subtype _ (by simp) f).symm
  have h2 : (Finset.univ.filter fun x : ι => x ≠ a ∧ x ≠ b) = Finset.univ \ {a, b} := by
    ext x; simp [not_or]
  rw [h1, h2, Finset.sum_sdiff_eq_sub (by simp), Finset.sum_pair hne]
  ring

omit [DecidableEq ι] in
/-- `D * D = 0`, entrywise. -/
private theorem sum_mul_eq_zero {D : Matrix ι ι k} (hD : D * D = 0) (r t : ι) :
    ∑ x, D r x * D x t = 0 := by
  simpa [Matrix.mul_apply] using congrFun (congrFun hD r) t

private theorem survivorProjection_mul_apply {μ : Type*} (M : Matrix ι μ k)
    (s : PairSurvivor a b) (y : μ) :
    (survivorProjection a b * M : Matrix (PairSurvivor a b) μ k) s y = M s.val y := by
  simp [Matrix.mul_apply, survivorProjection]

private theorem mul_survivorInclusion_apply {μ : Type*} [Fintype μ] (M : Matrix μ ι k)
    (x : μ) (s : PairSurvivor a b) :
    (M * survivorInclusion a b : Matrix μ (PairSurvivor a b) k) x s = M x s.val := by
  simp [Matrix.mul_apply, survivorInclusion]

private theorem mul_homotopy_apply {μ : Type*} (M : Matrix μ ι k) (x : μ) (y : ι) :
    (M * homotopy a b : Matrix μ ι k) x y = if y = a then M x b else 0 := by
  by_cases hy : y = a <;> simp [Matrix.mul_apply, homotopy, hy]

private theorem homotopy_mul_apply {μ : Type*} (M : Matrix ι μ k) (x : ι) (y : μ) :
    (homotopy a b * M : Matrix ι μ k) x y = if x = b then M a y else 0 := by
  by_cases hx : x = b <;> simp [Matrix.mul_apply, homotopy, hx]

end Entries

/-! ## Product forms -/

/-- The projection is `Q (1 - D H)`. -/
theorem projection_eq (D : Matrix ι ι k) (a b : ι) :
    projection D a b = survivorProjection a b * (1 - D * homotopy a b) := by
  ext s x
  rw [survivorProjection_mul_apply, Matrix.sub_apply, mul_homotopy_apply, Matrix.one_apply]
  rfl

/-- The inclusion is `(1 - H D) J`. -/
theorem inclusion_eq (D : Matrix ι ι k) (a b : ι) :
    inclusion D a b = (1 - homotopy a b * D) * survivorInclusion a b := by
  ext x s
  rw [mul_survivorInclusion_apply, Matrix.sub_apply, homotopy_mul_apply, Matrix.one_apply]
  rfl

/-- The reduced differential is `Q (D - D H D) J`. -/
theorem reducedDifferential_eq (D : Matrix ι ι k) (a b : ι) :
    reducedDifferential D a b =
      survivorProjection a b * (D - D * homotopy a b * D) * survivorInclusion a b := by
  ext r s
  rw [mul_survivorInclusion_apply, survivorProjection_mul_apply, Matrix.sub_apply,
    Matrix.mul_assoc, Matrix.mul_apply]
  simp only [homotopy_mul_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  rfl

/-- With `D a b = 1`, the reduced differential is `p D i`. -/
theorem reducedDifferential_eq_projection_mul_inclusion {D : Matrix ι ι k} {a b : ι}
    (hp : IsUnitPair D a b) :
    reducedDifferential D a b = projection D a b * D * inclusion D a b := by
  have hHDH : homotopy a b * D * homotopy a b = (homotopy a b : Matrix ι ι k) := by
    ext x y
    rw [mul_homotopy_apply, homotopy_mul_apply]
    by_cases hx : x = b <;> by_cases hy : y = a <;> simp [homotopy, hx, hy, hp.coeff]
  have key : (1 - D * homotopy a b) * D * (1 - homotopy a b * D) =
      D - D * homotopy a b * D := by
    have e : (1 - D * homotopy a b) * D * (1 - homotopy a b * D) =
        D - D * homotopy a b * D - D * homotopy a b * D +
          D * (homotopy a b * D * homotopy a b) * D := by
      noncomm_ring
    rw [e, hHDH]
    noncomm_ring
  rw [projection_eq, inclusion_eq, reducedDifferential_eq, ← key]
  simp only [Matrix.mul_assoc]

/-! ## Contraction identities -/

section Contraction

variable {D : Matrix ι ι k} {a b : ι}

/-- The reduced differential squares to zero. -/
theorem reducedDifferential_sq_zero (hD : D * D = 0) (hp : IsUnitPair D a b) :
    reducedDifferential D a b * reducedDifferential D a b = 0 := by
  ext r t
  simp only [Matrix.mul_apply, reducedDifferential, Matrix.zero_apply]
  rw [sum_pairSurvivor hp.ne (fun x => (D r x - D r b * D a x) * (D x t - D x b * D a t))]
  have e : ∀ x, (D r x - D r b * D a x) * (D x t - D x b * D a t) =
      D r x * D x t - D a t * (D r x * D x b) - D r b * (D a x * D x t)
        + D r b * D a t * (D a x * D x b) := fun x => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_mul_eq_zero hD, hp.coeff]
  ring

/-- The projection is a chain map: `p D = d' p`. -/
theorem projection_mul (hD : D * D = 0) (hp : IsUnitPair D a b) :
    projection D a b * D = reducedDifferential D a b * projection D a b := by
  ext s y
  simp only [Matrix.mul_apply, reducedDifferential, projection]
  rw [sum_pairSurvivor hp.ne (fun x => (D s x - D s b * D a x) *
    ((if x = y then 1 else 0) - if y = a then D x b else 0))]
  have hl : ∀ x, ((if s.val = x then (1 : k) else 0) - if x = a then D s b else 0) * D x y =
      (if s.val = x then D x y else 0) - (if x = a then D s b * D x y else 0) := fun x => by
    split_ifs <;> ring
  have hr : ∀ x, (D s x - D s b * D a x) *
      ((if x = y then (1 : k) else 0) - if y = a then D x b else 0) =
      (if x = y then D s x - D s b * D a x else 0) -
        (if y = a then D s x * D x b - D s b * (D a x * D x b) else 0) := fun x => by
    split_ifs <;> ring
  simp only [hl, hr, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  have hs : ∑ x, (if y = a then D s x * D x b - D s b * (D a x * D x b) else 0) = 0 := by
    by_cases h : y = a
    · simp only [h, ite_true, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_mul_eq_zero hD,
        mul_zero, sub_zero]
    · simp [h]
  rw [hs, hp.coeff]
  by_cases h : y = a
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The inclusion is a chain map: `D i = i d'`. -/
theorem mul_inclusion (hD : D * D = 0) (hp : IsUnitPair D a b) :
    D * inclusion D a b = inclusion D a b * reducedDifferential D a b := by
  ext x s
  simp only [Matrix.mul_apply, reducedDifferential, inclusion]
  rw [sum_pairSurvivor hp.ne (fun y => ((if x = y then 1 else 0) - if x = b then D a y else 0)
    * (D y s - D y b * D a s))]
  have hl : ∀ y, D x y * ((if y = s.val then (1 : k) else 0) - if y = b then D a s else 0) =
      (if y = s.val then D x y else 0) - (if y = b then D x y * D a s else 0) := fun y => by
    split_ifs <;> ring
  have hr : ∀ y, ((if x = y then (1 : k) else 0) - if x = b then D a y else 0) *
      (D y s - D y b * D a s) =
      (if x = y then D y s - D y b * D a s else 0) -
        (if x = b then D a y * D y s - D a s * (D a y * D y b) else 0) := fun y => by
    split_ifs <;> ring
  simp only [hl, hr, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  have hs : ∑ y, (if x = b then D a y * D y s - D a s * (D a y * D y b) else 0) = 0 := by
    by_cases h : x = b
    · simp only [h, ite_true, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_mul_eq_zero hD,
        mul_zero, sub_zero]
    · simp [h]
  rw [hs, hp.coeff]
  by_cases h : x = b
  · subst h; simp; ring
  · simp [h]

/-- `p i = 1`. -/
theorem projection_mul_inclusion (hne : a ≠ b) :
    projection D a b * inclusion D a b = 1 := by
  ext s t
  simp only [Matrix.mul_apply, projection, inclusion, Matrix.one_apply]
  have e : ∀ x, ((if s.val = x then (1 : k) else 0) - if x = a then D s b else 0) *
      ((if x = t.val then 1 else 0) - if x = b then D a t else 0) =
      (if s.val = x then (if x = t.val then 1 else 0) - (if x = b then D a t else 0) else 0) -
        (if x = a then D s b * ((if x = t.val then 1 else 0) - if x = b then D a t else 0)
          else 0) := fun x => by
    split_ifs <;> ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, s.2.2, t.2.1.symm, hne, ite_false, sub_zero, mul_zero]
  simp [Subtype.ext_iff]

/-- `1 - i p = D H + H D`. -/
theorem one_sub_inclusion_mul_projection (hD : D * D = 0) (hp : IsUnitPair D a b) :
    1 - inclusion D a b * projection D a b = D * homotopy a b + homotopy a b * D := by
  ext x y
  rw [Matrix.add_apply, mul_homotopy_apply, homotopy_mul_apply]
  simp only [Matrix.mul_apply, Matrix.sub_apply, inclusion, projection, Matrix.one_apply]
  set A : ι → k := fun z => (if x = z then (1 : k) else 0) - if x = b then D a z else 0
  set B : ι → k := fun z => (if z = y then (1 : k) else 0) - if y = a then D z b else 0
  rw [sum_pairSurvivor hp.ne (fun z => A z * B z)]
  have hAb : A b = 0 := by
    by_cases hx : x = b <;> simp [A, hx, hp.coeff]
  have hBa : B a = 0 := by
    by_cases hy : y = a <;> simp [B, hy, hp.coeff, eq_comm]
  have hfull : ∑ z, A z * B z = (if x = y then 1 else 0) - (if y = a then D x b else 0)
      - (if x = b then D a y else 0) := by
    have e : ∀ z, A z * B z = (if x = z then (if z = y then (1 : k) else 0) else 0)
        - (if x = z then (if y = a then D z b else 0) else 0)
        - (if x = b then D a z * (if z = y then 1 else 0) else 0)
        + (if x = b then (if y = a then D a z * D z b else 0) else 0) := fun z => by
      simp only [A, B]
      split_ifs <;> ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    by_cases h2 : x = b <;> by_cases h3 : y = a <;> simp [h2, h3, sum_mul_eq_zero hD a b]
  rw [hfull, hAb, hBa, mul_zero, zero_mul]
  by_cases h2 : x = b <;> by_cases h3 : y = a <;> simp [h2, h3, Ne.symm hp.ne]
  ring

/-- `H H = 0`. -/
theorem homotopy_mul_homotopy (hne : a ≠ b) :
    (homotopy a b : Matrix ι ι k) * homotopy a b = 0 := by
  ext x y
  rw [mul_homotopy_apply]
  simp [homotopy, Ne.symm hne]

/-- `p H = 0`. -/
theorem projection_mul_homotopy (hne : a ≠ b) :
    projection D a b * (homotopy a b : Matrix ι ι k) = 0 := by
  ext s y
  rw [mul_homotopy_apply]
  simp [projection, s.2.2, Ne.symm hne]

/-- `H i = 0`. -/
theorem homotopy_mul_inclusion (hne : a ≠ b) :
    (homotopy a b : Matrix ι ι k) * inclusion D a b = 0 := by
  ext x s
  rw [homotopy_mul_apply]
  simp [inclusion, s.2.1.symm, hne]

end Contraction

/-! ## Degrees -/

section Degrees

variable {degree : ι → ℕ} {D : Matrix ι ι k} {a b : ι}

omit [DecidableEq ι] in
/-- The reduced differential lowers the inherited degree by one. -/
theorem reducedDifferential_lowersDegree (hD : IsBasedDifferential degree D)
    (hp : IsUnitPair D a b) (r s : PairSurvivor a b)
    (h : reducedDifferential D a b r s ≠ 0) :
    degree s.val = degree r.val + 1 := by
  by_cases h1 : D r s = 0
  · have h2 : D r b * D a s ≠ 0 := by simpa [reducedDifferential, h1] using h
    have : Nontrivial k := ⟨⟨_, _, h2⟩⟩
    have hab := hD.lowers_degree a b (by rw [hp.coeff]; exact one_ne_zero)
    rw [hD.lowers_degree _ _ (right_ne_zero_of_mul h2),
      ← hD.lowers_degree _ _ (left_ne_zero_of_mul h2), hab]
  · exact hD.lowers_degree _ _ h1

/-- The projection preserves degree on its support. -/
theorem projection_degree (hD : IsBasedDifferential degree D) (hp : IsUnitPair D a b)
    (s : PairSurvivor a b) (x : ι) (h : projection D a b s x ≠ 0) :
    degree s.val = degree x := by
  by_cases hx : x = a
  · subst hx
    have h2 : D s b ≠ 0 := by
      intro h0; apply h; simp [projection, s.2.1, h0]
    have : Nontrivial k := ⟨⟨_, _, h2⟩⟩
    have hab := hD.lowers_degree _ b (by rw [hp.coeff]; exact one_ne_zero)
    have := hD.lowers_degree _ _ h2
    omega
  · have : s.val = x := by
      by_contra hs; apply h; simp [projection, hs, hx]
    rw [this]

/-- The inclusion preserves degree on its support. -/
theorem inclusion_degree (hD : IsBasedDifferential degree D) (hp : IsUnitPair D a b)
    (x : ι) (s : PairSurvivor a b) (h : inclusion D a b x s ≠ 0) :
    degree x = degree s.val := by
  by_cases hx : x = b
  · subst hx
    have h2 : D a s ≠ 0 := by
      intro h0; apply h; simp [inclusion, Ne.symm s.2.2, h0]
    have : Nontrivial k := ⟨⟨_, _, h2⟩⟩
    have hab := hD.lowers_degree a _ (by rw [hp.coeff]; exact one_ne_zero)
    have := hD.lowers_degree _ _ h2
    omega
  · have : x = s.val := by
      by_contra hs; apply h; simp [inclusion, hs, hx]
    rw [this]

/-- The homotopy raises degree by one on its support. -/
theorem homotopy_degree (hD : IsBasedDifferential degree D) (hp : IsUnitPair D a b)
    (x y : ι) (h : (homotopy a b : Matrix ι ι k) x y ≠ 0) : degree x = degree y + 1 := by
  have hxy : x = b ∧ y = a := by
    by_contra hn; apply h; simp [homotopy, hn]
  have : Nontrivial k := ⟨⟨_, _, h⟩⟩
  rw [hxy.1, hxy.2]
  exact hD.lowers_degree a b (by rw [hp.coeff]; exact one_ne_zero)

/-- The reduced differential is a based differential for the inherited degree. -/
theorem isBasedDifferential_reduced (hD : IsBasedDifferential degree D)
    (hp : IsUnitPair D a b) :
    IsBasedDifferential (degree ∘ Subtype.val) (reducedDifferential D a b) :=
  ⟨reducedDifferential_sq_zero hD.sq_zero hp, reducedDifferential_lowersDegree hD hp⟩

end Degrees

/-! ## Filtration -/

section Filtration

variable {grade : ι → ℤ} {D : Matrix ι ι k} {a b : ι}

omit [Fintype ι] [DecidableEq ι] in
/-- For an equal-grade pair, the reduced differential does not increase grades. -/
theorem reducedDifferential_gradeNonincreasing (hD : GradeNonincreasing grade grade D)
    (hg : grade a = grade b) :
    GradeNonincreasing (grade ∘ Subtype.val) (grade ∘ Subtype.val)
      (reducedDifferential D a b) := by
  intro r s h
  by_cases h1 : D r s = 0
  · have h2 : D r b * D a s ≠ 0 := by simpa [reducedDifferential, h1] using h
    exact (hD _ _ (left_ne_zero_of_mul h2)).trans (hg ▸ hD _ _ (right_ne_zero_of_mul h2))
  · exact hD _ _ h1

omit [Fintype ι] in
/-- For an equal-grade pair, the projection does not increase grades. -/
theorem projection_gradeNonincreasing (hD : GradeNonincreasing grade grade D)
    (hg : grade a = grade b) :
    GradeNonincreasing (grade ∘ Subtype.val) grade (projection D a b) := by
  intro s x h
  by_cases hx : x = a
  · subst hx
    have h2 : D s b ≠ 0 := by
      intro h0; apply h; simp [projection, s.2.1, h0]
    exact (hD _ _ h2).trans hg.ge
  · have : s.val = x := by
      by_contra hs; apply h; simp [projection, hs, hx]
    exact le_of_eq (congrArg grade this)

omit [Fintype ι] in
/-- For an equal-grade pair, the inclusion does not increase grades. -/
theorem inclusion_gradeNonincreasing (hD : GradeNonincreasing grade grade D)
    (hg : grade a = grade b) :
    GradeNonincreasing grade (grade ∘ Subtype.val) (inclusion D a b) := by
  intro x s h
  by_cases hx : x = b
  · subst hx
    have h2 : D a s ≠ 0 := by
      intro h0; apply h; simp [inclusion, Ne.symm s.2.2, h0]
    exact hg.symm.le.trans (hD _ _ h2)
  · have : x = s.val := by
      by_contra hs; apply h; simp [inclusion, hs, hx]
    exact le_of_eq (congrArg grade this)

omit [Fintype ι] in
/-- For an equal-grade pair, the homotopy does not increase grades. -/
theorem homotopy_gradeNonincreasing (hg : grade a = grade b) :
    GradeNonincreasing grade grade (homotopy a b : Matrix ι ι k) := by
  intro x y h
  have hxy : x = b ∧ y = a := by
    by_contra hn; apply h; simp [homotopy, hn]
  rw [hxy.1, hxy.2, hg]

/-- Cancelling an equal-grade unit pair of a filtered differential leaves a filtered
differential on the survivors, with inherited degree and grade. -/
theorem isFilteredDifferential_reduced {degree : ι → ℕ}
    (hD : IsFilteredDifferential degree grade D) (hp : IsUnitPair D a b)
    (hg : grade a = grade b) :
    IsFilteredDifferential (degree ∘ Subtype.val) (grade ∘ Subtype.val)
      (reducedDifferential D a b) :=
  ⟨isBasedDifferential_reduced hD.toIsBasedDifferential hp,
    reducedDifferential_gradeNonincreasing hD.grade_le hg⟩

end Filtration

/-- The finite-input boundary is a filtered differential with list grades. -/
theorem isFilteredDifferential_boundary (xs : FiniteInput.Input) (h : FiniteInput.Valid xs) :
    IsFilteredDifferential (FiniteInput.degree xs) (fun i => (xs.get i).2)
      (FiniteInput.boundary xs) := by
  refine ⟨⟨FiniteInput.boundary_sq_zero xs h, FiniteInput.boundary_lowersDegree xs h⟩, ?_⟩
  intro r c hrc
  exact h.2.2.2.2 r c (le_of_lt (FiniteInput.boundary_strict xs h r c hrc))

end TDA.Persistence.Morse.Cancellation
