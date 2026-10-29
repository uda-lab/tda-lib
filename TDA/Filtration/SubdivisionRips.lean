import TDA.Filtration.CechSupNorm
import Mathlib.Order.OrderDual
import Mathlib.Data.NNReal.Basic

/-!
# Normalized subdivision-Rips bifiltrations

A vertex of the subdivision is a nonempty finite simplex of the original
complex. Faces are finite flags, represented without a chosen enumeration by
pairwise comparable simplices. Requiring the normalized cardinality bound on
every member of a flag is equivalent to requiring it on its least member.
The radius convention is the open condition `dist x y < 2 * r`.

The index has strictly positive mass and radius. Its mass coordinate is ordered
oppositely, so decreasing mass and increasing radius give inclusions.
-/

open scoped NNReal ENNReal

universe u w

namespace TDA.Filtration.SubdivisionRips

/-- Strictly positive real coordinates; no zero-threshold extension is made. -/
abbrev Positive := {x : ℝ // 0 < x}

/-- Density decreases and radius increases along structure maps. -/
structure Index where
  /-- Positive mass coordinate, with opposite order. -/
  density : Positiveᵒᵈ
  /-- Positive radius coordinate. -/
  scale : Positive

/-- The numerical mass coordinate. -/
def mass (p : Index) : ℝ := (OrderDual.ofDual p.density).val

/-- The numerical ball radius. -/
def radius (p : Index) : ℝ := p.scale.val

/-- Every admitted index has strictly positive mass. -/
@[simp] theorem mass_pos (p : Index) : 0 < mass p := (OrderDual.ofDual p.density).property

/-- Every admitted index has strictly positive radius. -/
@[simp] theorem radius_pos (p : Index) : 0 < radius p := p.scale.property

instance : Preorder Index where
  le p q := mass q ≤ mass p ∧ radius p ≤ radius q
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h g := ⟨g.1.trans h.1, h.2.trans g.2⟩

@[simp] theorem index_le_iff (p q : Index) :
    p ≤ q ↔ mass q ≤ mass p ∧ radius p ≤ radius q := Iff.rfl

variable {V : Type u}

/-- Subdivision at a normalized mass threshold, on the fixed ambient type of
finite vertex sets. Empty simplices cannot be subdivision vertices. -/
def subdivision [Fintype V] (K : PreAbstractSimplicialComplex V) (k : ℝ) :
    PreAbstractSimplicialComplex (Finset V) where
  faces := {S | S.Nonempty ∧
    (∀ s ∈ S, s ∈ K ∧ k ≤ (s.card : ℝ) / Fintype.card V) ∧
    ∀ s ∈ S, ∀ t ∈ S, s ⊆ t ∨ t ⊆ s}
  isRelLowerSet_faces := by
    intro S hS
    exact ⟨hS.1, fun T hTS hT => ⟨hT,
      fun s hs => hS.2.1 s (hTS hs),
      fun s hs t ht => hS.2.2 s (hTS hs) t (hTS ht)⟩⟩

/-- Flags are nonempty, consist of sufficiently large original faces, and are
linearly ordered by inclusion. -/
theorem mem_subdivision_iff [Fintype V] (K : PreAbstractSimplicialComplex V)
    (k : ℝ) (S : Finset (Finset V)) :
    S ∈ subdivision K k ↔ S.Nonempty ∧
      (∀ s ∈ S, s ∈ K ∧ k ≤ (s.card : ℝ) / Fintype.card V) ∧
      ∀ s ∈ S, ∀ t ∈ S, s ⊆ t ∨ t ⊆ s := Iff.rfl

/-- On a flag with least member `s₀`, checking its normalized size checks
exactly the source's minimum-simplex condition. -/
theorem mem_subdivision_iff_of_least [Fintype V] (K : PreAbstractSimplicialComplex V)
    (k : ℝ) (S : Finset (Finset V)) {s₀ : Finset V} (hs₀ : s₀ ∈ S)
    (hleast : ∀ s ∈ S, s₀ ⊆ s) :
    S ∈ subdivision K k ↔
      (∀ s ∈ S, s ∈ K) ∧ k ≤ (s₀.card : ℝ) / Fintype.card V ∧
      ∀ s ∈ S, ∀ t ∈ S, s ⊆ t ∨ t ⊆ s := by
  constructor
  · intro h
    exact ⟨fun s hs => (h.2.1 s hs).1, (h.2.1 s₀ hs₀).2, h.2.2⟩
  · rintro ⟨hK, hk, hchain⟩
    refine ⟨⟨s₀, hs₀⟩, fun s hs => ⟨hK s hs, hk.trans ?_⟩, hchain⟩
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card (hleast s hs))
      (by positivity)

/-- Subdivision is natural for simultaneous enlargement of the complex and
lowering of the mass threshold. -/
theorem subdivision_mono [Fintype V] {K L : PreAbstractSimplicialComplex V}
    {k l : ℝ} (hKL : K ≤ L) (hlk : l ≤ k) :
    subdivision K k ≤ subdivision L l := by
  intro S hS
  exact ⟨hS.1, fun s hs => ⟨hKL (hS.2.1 s hs).1,
    hlk.trans (hS.2.1 s hs).2⟩, hS.2.2⟩

/-- A normalized threshold above one removes every flag of a nonempty finite
carrier, independent of the underlying complex. -/
theorem subdivision_eq_bot_of_one_lt [Fintype V] [Nonempty V]
    (K : PreAbstractSimplicialComplex V) {k : ℝ} (hk : 1 < k) :
    subdivision K k = ⊥ := by
  apply le_antisymm _ bot_le
  intro S hS
  obtain ⟨s, hs⟩ := hS.1
  have hsize : (s.card : ℝ) / Fintype.card V ≤ 1 := by
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).2
    exact_mod_cast Finset.card_le_univ s
  exact (not_le_of_gt hk) ((hS.2.1 s hs).2.trans hsize)

/-- At normalized mass one, an existing full-carrier simplex gives exactly
one subdivision vertex. This is a useful nonzero homology test stage. -/
theorem subdivision_one_eq_singleton [Fintype V] [Nonempty V]
    (K : PreAbstractSimplicialComplex V) (hK : Finset.univ ∈ K) :
    subdivision K 1 = singletonFace (Finset.univ : Finset V) := by
  have hd : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  apply le_antisymm
  · intro S hS
    have hfull : ∀ s ∈ S, s = Finset.univ := by
      intro s hs
      have hsize := (hS.2.1 s hs).2
      have hge : (Fintype.card V : ℝ) ≤ s.card := by
        simpa using (le_div_iff₀ hd).mp hsize
      apply Finset.eq_univ_of_card
      apply le_antisymm (Finset.card_le_univ s)
      exact_mod_cast hge
    apply (mem_singletonFace_iff _ _).2
    obtain ⟨s, hs⟩ := hS.1
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hfull s hs ▸ hs, hfull⟩
  · intro S hS
    rw [(mem_singletonFace_iff _ _).mp hS]
    apply (mem_subdivision_iff K 1 {Finset.univ}).2
    simp [hK, ne_of_gt hd]

/-- The source's open-radius Rips complex, including its nonempty-face guard. -/
def openRips (d : MetricSpace V) (r : ℝ) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ ∀ v ∈ s, ∀ w ∈ s, d.dist v w < 2 * r}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht,
      fun v hv w hw => hs.2 v (hts hv) w (hts hw)⟩⟩

/-- Open Rips face membership uses ball radius, rather than diameter time. -/
theorem mem_openRips_iff (d : MetricSpace V) (r : ℝ) (s : Finset V) :
    s ∈ openRips d r ↔ s.Nonempty ∧
      ∀ v ∈ s, ∀ w ∈ s, d.dist v w < 2 * r := Iff.rfl

/-- Increasing radius preserves open Rips faces. -/
theorem openRips_mono (d : MetricSpace V) {r q : ℝ} (h : r ≤ q) :
    openRips d r ≤ openRips d q := by
  intro s hs
  exact ⟨hs.1, fun v hv w hw => (hs.2 v hv w hw).trans_le (by linarith)⟩

/-- The normalized subdivision-Rips bifiltration of a finite metric carrier. -/
def bifiltration [Fintype V] (d : MetricSpace V) :
    SimplicialFiltration Index (Finset V) where
  toFun p := subdivision (openRips d (radius p)) (mass p)
  monotone' := by
    intro p q hpq
    exact subdivision_mono (openRips_mono d hpq.2) hpq.1

/-- Every stage of the normalized bifiltration is the concrete flag complex. -/
theorem bifiltration_apply [Fintype V] (d : MetricSpace V) (p : Index) :
    bifiltration d p = subdivision (openRips d (radius p)) (mass p) := rfl

/-- At positive radius, membership is equivalently the strict diameter bound.
This makes the factor of two against the existing closed-diameter API explicit. -/
theorem mem_openRips_iff_diameter_lt (d : MetricSpace V) {r : ℝ} (hr : 0 < r)
    (s : Finset V) :
    s ∈ openRips d r ↔ s.Nonempty ∧ Rips.diameter d s < 2 * r := by
  classical
  rw [mem_openRips_iff]
  simp only [Rips.diameter, Finset.fold_max_lt, Finset.mem_product]
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨hs, by linarith, fun p hp => h p.1 hp.1 p.2 hp.2⟩
  · rintro ⟨hs, _, h⟩
    exact ⟨hs, fun v hv w hw => h (v, w) ⟨hv, hw⟩⟩

/-- The nerve of open ambient balls, retaining labels and empty-stage support. -/
def openCech {X : Type w} [PseudoMetricSpace X] (p : V → X) (r : ℝ) :
    PreAbstractSimplicialComplex V :=
  TDA.Topology.nerve (fun v => Metric.ball (p v) r)

/-- A common open-ball witness is exactly an open Čech face. -/
theorem mem_openCech_iff {X : Type w} [PseudoMetricSpace X] (p : V → X)
    (r : ℝ) (s : Finset V) :
    s ∈ openCech p r ↔ s.Nonempty ∧ ∃ x, ∀ v ∈ s, dist x (p v) < r := Iff.rfl

/-- In a finite sup-norm product, open Čech equals the open-radius Rips
complex. The existing coordinatewise Helly witness is used at an intermediate
closed radius strictly below `r`, so boundary faces are not inserted. -/
theorem openCech_eq_openRips {ι : Type w} [Fintype ι] (d : MetricSpace V)
    (p : V → ι → ℝ) (hd : ∀ v w, d.dist v w = dist (p v) (p w))
    {r : ℝ} (hr : 0 < r) : openCech p r = openRips d r := by
  classical
  apply le_antisymm
  · intro s hs
    obtain ⟨hs, x, hx⟩ := (mem_openCech_iff p r s).mp hs
    refine ⟨hs, fun v hv w hw => ?_⟩
    rw [hd]
    exact (dist_triangle_left (p v) (p w) x).trans_lt (by linarith [hx v hv, hx w hw])
  · intro s hs
    have hdiam := ((mem_openRips_iff_diameter_lt d hr s).mp hs).2
    let q := (Rips.diameter d s / 2 + r) / 2
    have hqr : q < r := by dsimp [q]; linarith
    have hpair : ∀ v ∈ s, ∀ w ∈ s, dist (p v) (p w) ≤ 2 * q := by
      intro v hv w hw
      rw [← hd]
      have := Rips.dist_le_diameter d hv hw
      dsimp [q]
      linarith
    exact ⟨hs.1, Cech.supNormWitness p q s hs.1,
      fun v hv => (Cech.dist_supNormWitness_le p hs.1 hpair hv).trans_lt hqr⟩

/-- The equality of open Čech and Rips holds after normalized subdivision,
using exactly the same flags and normalization. -/
theorem subdivision_openCech_eq {ι : Type w} [Fintype ι] [Fintype V]
    (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (a : Index) :
    subdivision (openCech p (radius a)) (mass a) = bifiltration d a := by
  have hr : 0 < radius a := radius_pos a
  rw [openCech_eq_openRips d p hd hr]
  rfl

/-- Finite distance coordinates give the finite-dimensional Kuratowski map. -/
def distanceCoordinates (d : MetricSpace V) (v : V) : V → ℝ := fun w => d.dist w v

/-- The finite distance-coordinate map preserves distances exactly. -/
theorem distanceCoordinates_dist [Fintype V] (d : MetricSpace V) (v w : V) :
    dist (distanceCoordinates d v) (distanceCoordinates d w) = d.dist v w := by
  let : MetricSpace V := d
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).2
    intro z
    simpa only [distanceCoordinates, Real.dist_eq, dist_comm z] using abs_dist_sub_le v w z
  · have h := dist_le_pi_dist (distanceCoordinates d v) (distanceCoordinates d w) v
    simpa [distanceCoordinates, Real.dist_eq] using h

/-- The finite Kuratowski map is an isometric embedding into a finite sup-norm
product, without a choice of separability data. -/
theorem isometry_distanceCoordinates [Fintype V] (d : MetricSpace V) :
    @Isometry V (V → ℝ) d.toPseudoMetricSpace.toPseudoEMetricSpace inferInstance
      (distanceCoordinates d) := by
  let : MetricSpace V := d
  exact Isometry.of_dist_eq (distanceCoordinates_dist d)

/-- A raw additive distance bound transports concrete flags, with the factor
of two corresponding to the source's ball-radius convention. -/
theorem bifiltration_le_of_dist_le [Fintype V] (d e : MetricSpace V) (δ : ℝ≥0)
    (hde : ∀ v w, e.dist v w ≤ d.dist v w + 2 * δ)
    {p q : Index} (hk : mass q ≤ mass p) (hr : radius p + δ ≤ radius q) :
    bifiltration d p ≤ bifiltration e q := by
  apply subdivision_mono ?_ hk
  intro s hs
  exact ⟨hs.1, fun v hv w hw => by
    have := hs.2 v hv w hw
    have := hde v w
    linarith⟩

section Relabel
variable {W : Type w}

/-- Relabelling original vertices induces an injective relabelling of the
ambient subdivision vertices. -/
def relabelVertex (e : V ≃ W) : Finset V ↪ Finset W :=
  ⟨Finset.map e.toEmbedding, Finset.map_injective e.toEmbedding⟩

/-- Normalized subdivision is invariant under a bijection preserving original
faces. Both simplex sizes and the carrier normalization are preserved. -/
theorem mem_subdivision_relabel_iff [Fintype V] [Fintype W] (e : V ≃ W)
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hKL : ∀ s, s.map e.toEmbedding ∈ L ↔ s ∈ K) (k : ℝ)
    (S : Finset (Finset V)) :
    S.map (relabelVertex e) ∈ subdivision L k ↔ S ∈ subdivision K k := by
  simp only [mem_subdivision_iff, Finset.map_nonempty, Finset.forall_mem_map,
    relabelVertex, Function.Embedding.coeFn_mk, Finset.card_map, Finset.map_subset_map, hKL, ← Fintype.card_congr e]

/-- Isometric bijections preserve every open Rips face at exactly the same
radius. -/
theorem mem_openRips_relabel_iff (e : V ≃ W) (d : MetricSpace V) (f : MetricSpace W)
    (h : ∀ v w, f.dist (e v) (e w) = d.dist v w) (r : ℝ) (s : Finset V) :
    s.map e.toEmbedding ∈ openRips f r ↔ s ∈ openRips d r := by
  simp only [mem_openRips_iff, Finset.map_nonempty, Finset.forall_mem_map,
    Equiv.coe_toEmbedding, h]

/-- The concrete normalized flag faces do not depend on an isometric
relabelling of a finite metric input. -/
theorem mem_bifiltration_relabel_iff [Fintype V] [Fintype W] (e : V ≃ W)
    (d : MetricSpace V) (f : MetricSpace W)
    (h : ∀ v w, f.dist (e v) (e w) = d.dist v w)
    (p : Index) (S : Finset (Finset V)) :
    S.map (relabelVertex e) ∈ bifiltration f p ↔ S ∈ bifiltration d p :=
  mem_subdivision_relabel_iff e _ _ (mem_openRips_relabel_iff e d f h (radius p)) (mass p) S

end Relabel

end TDA.Filtration.SubdivisionRips
