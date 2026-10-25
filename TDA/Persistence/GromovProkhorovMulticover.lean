import TDA.Topology.FiniteGromovProkhorovWitness
import TDA.Persistence.MulticoverNerve

/-!
# SR homology comparisons on a common GP ambient

A concrete GP witness supplies natural maps from both normalized
subdivision-Rips homology diagrams to their large-face cover nerves, using
the same finite sup-norm ambient as its spatial multicover interleaving. The
large-face nerve homology diagrams themselves form a concrete restricted
interleaving over the two-copy positive index.
-/

set_option autoImplicit false
open scoped NNReal ENNReal
universe u v w
namespace TDA.Topology.FiniteGromovProkhorov
noncomputable section
open CategoryTheory TDA.Topology.MeasureBifiltration
open MeasureTheory Metric
open TDA.Filtration.SubdivisionRips
variable {X : Type u} {Y : Type u} [MetricSpace X] [MetricSpace Y]
variable [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
open TDA.Persistence TDA.Persistence.SubdivisionRips TDA.Simplicial
attribute [local instance] TDA.Persistence.SubdivisionRips.vertexOrder
local instance : DecidableEq X := Classical.decEq X
local instance : DecidableEq Y := Classical.decEq Y

/-- The same GP witness gives the concrete natural comparison from the first
normalized SR homology diagram to its large-face cover nerve homology. -/
noncomputable def SupNormWitness.leftHomologyComparison {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    homology R (inferInstance : MetricSpace X) n ⟶
      simplicialHomologyPModule R (largeFaceNerveBifiltration s.left) n :=
  ripsHomologyToLargeFaceNerve R _ s.left
    (fun x x' => (s.left_isometry.dist_eq x x').symm) n

/-- The second normalized SR module has its corresponding actual comparison
on the same ambient used by the interleaving. -/
noncomputable def SupNormWitness.rightHomologyComparison {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    homology R (inferInstance : MetricSpace Y) n ⟶
      simplicialHomologyPModule R (largeFaceNerveBifiltration s.right) n :=
  ripsHomologyToLargeFaceNerve R _ s.right
    (fun y y' => (s.right_isometry.dist_eq y y').symm) n

/-- The normalized subdivision-Rips homology diagram of a finite metric is
naturally isomorphic to the large-face nerve diagram of any isometric finite
coordinate realization. -/
noncomputable def ripsHomologyToLargeFaceNerveIso {V : Type u} [Fintype V]
    (R : Type w) [Ring R] (d : MetricSpace V) {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ) :
    homology R d n ≅ simplicialHomologyPModule R (largeFaceNerveBifiltration p) n :=
  (eqToIso (cechHomology_eq R d p hd n).symm) ≪≫
    cechHomologyToLargeFaceNerveIso R p n

private noncomputable def nearXYLabel {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (S : Finset X) : Finset Y :=
  Finset.univ.filter fun y => ∃ x ∈ S,
    dist (s.right y) (s.left x) < (δ : ℝ)

private noncomputable def nearYXLabel {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (T : Finset Y) : Finset X :=
  Finset.univ.filter fun x => ∃ y ∈ T,
    dist (s.left x) (s.right y) < (δ : ℝ)

private theorem labelCount_image_eq_card {A : Type*} {Z : Type*} [Fintype A]
    (p : A → Z) (hp : Function.Injective p) (S : Finset A) :
    labelCount p (p '' (S : Set A)) = S.card := by
  classical
  unfold labelCount
  have hfilter : Finset.univ.filter (fun a => p a ∈ p '' (S : Set A)) = S := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change p a ∈ p '' (S : Set A) ↔ a ∈ S
    rw [Set.mem_image]
    constructor
    · rintro ⟨b, hb, hba⟩
      have : b = a := hp hba
      simpa [this] using hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  rw [hfilter]

private theorem nearLabel_mass_lower_bound {δ : ℝ≥0}
    {A : Type*} {B : Type*} {Z : Type*} [MetricSpace Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (p : A → Z) (q : B → Z) (hp : Function.Injective p) (hq : Function.Injective q)
    (hcost : levyProkhorovEDist (uniformMeasure p) (uniformMeasure q) <
      (δ : ℝ≥0∞))
    (S : Finset A) (T : Finset B)
    (hnear : ∀ b, b ∈ T ↔ ∃ a ∈ S, dist (q b) (p a) < (δ : ℝ))
    {a b : Index}
    (hlarge : mass a ≤ (S.card : ℝ) / Fintype.card A)
    (hcross : mass b + δ ≤ mass a) :
    mass b ≤ (T.card : ℝ) / Fintype.card B := by
  classical
  letI : MeasurableSpace Z := ‹MeasurableSpace Z›
  let leftImage : Set Z := p '' (S : Set A)
  let thickImage : Set Z := Metric.thickening (δ : ℝ) leftImage
  let rightImage : Set Z := q '' (T : Set B)
  have hleftFinite : leftImage.Finite := S.finite_toSet.image p
  have hrightFinite : rightImage.Finite := T.finite_toSet.image q
  have hleftMeas : MeasurableSet leftImage := hleftFinite.measurableSet
  have hthickMeas : MeasurableSet thickImage := isOpen_thickening.measurableSet
  have hrightMeas : MeasurableSet rightImage := hrightFinite.measurableSet
  have hLP := left_measure_le_of_levyProkhorovEDist_lt hcost hleftMeas
  have hsupported : uniformMeasure q thickImage ≤ uniformMeasure q rightImage :=
    uniformMeasure_apply_le_of_label_mem q q hthickMeas hrightMeas (by
      intro y hy
      obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
      change z ∈ p '' (S : Set A) at hz
      rcases (Set.mem_image p (S : Set A) z).mp hz with ⟨x, hx, rfl⟩
      have hynear : y ∈ T := (hnear y).2 ⟨x, hx, hyz⟩
      exact ⟨y, hynear, rfl⟩)
  have hmeasure : uniformMeasure p leftImage ≤ uniformMeasure q rightImage + (δ : ℝ≥0∞) :=
    hLP.trans (add_le_add hsupported le_rfl)
  have hmeasureReal := ENNReal.toReal_mono (by finiteness) hmeasure
  have hreal : (uniformMeasure p).real leftImage ≤
      (uniformMeasure q).real rightImage + (δ : ℝ) := by
    simpa only [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.coe_ne_top,
      ENNReal.coe_toReal, Measure.real] using hmeasureReal
  rw [uniformMeasure_real p hleftMeas, labelCount_image_eq_card p hp S,
    uniformMeasure_real q hrightMeas, labelCount_image_eq_card q hq T] at hreal
  linarith

private theorem nearXY_mass_lower_bound {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) {a b : Index} (S : Finset X)
    (hlarge : mass a ≤ (S.card : ℝ) / Fintype.card X)
    (hcross : mass b + δ ≤ mass a) :
    mass b ≤ ((nearXYLabel s S).card : ℝ) / Fintype.card Y := by
  classical
  letI : MeasurableSpace ((X ⊕ Y) → ℝ) := borel _
  letI : BorelSpace ((X ⊕ Y) → ℝ) := ⟨rfl⟩
  apply nearLabel_mass_lower_bound s.left s.right s.left_isometry.injective
    s.right_isometry.injective s.cost_lt S (nearXYLabel s S) ?_ hlarge hcross
  intro y
  simp only [nearXYLabel, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem nearYX_mass_lower_bound {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) {a b : Index} (T : Finset Y)
    (hlarge : mass a ≤ (T.card : ℝ) / Fintype.card Y)
    (hcross : mass b + δ ≤ mass a) :
    mass b ≤ ((nearYXLabel s T).card : ℝ) / Fintype.card X := by
  classical
  letI : MeasurableSpace ((X ⊕ Y) → ℝ) := borel _
  letI : BorelSpace ((X ⊕ Y) → ℝ) := ⟨rfl⟩
  apply nearLabel_mass_lower_bound s.right s.left s.right_isometry.injective
    s.left_isometry.injective (by simpa only [levyProkhorovEDist_comm] using s.cost_lt)
    T (nearYXLabel s T) ?_ hlarge hcross
  intro x
  simp only [nearYXLabel, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem finset_nonempty_of_positive_mass {V : Type*} [Fintype V] [Nonempty V]
    (a : Index) (S : Finset V) (hS : mass a ≤ (S.card : ℝ) / Fintype.card V) :
    S.Nonempty := by
  by_contra hne
  have hEq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hzero : mass a ≤ 0 := by simpa [hEq] using hS
  exact (not_le_of_gt (mass_pos a)) hzero

private noncomputable def nearXYVertexMap {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (a b : Index)
    (h : mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b) :
    VertexMap (TDA.Topology.nerve (largeFaceCover s.left a))
      (TDA.Topology.nerve (largeFaceCover s.right b)) where
  toFun := nearXYLabel s
  map_face := by
    classical
    letI : DecidableEq (Finset Y) := Classical.decEq _
    intro C hC
    obtain ⟨hCne, hCvalid, hCcenter⟩ := (mem_largeFaceNerve_iff s.left a C).mp hC
    obtain ⟨_, center, hcenter⟩ := hCcenter
    change C.image (nearXYLabel s) ∈ TDA.Topology.nerve (largeFaceCover s.right b)
    apply (mem_largeFaceNerve_iff s.right b _).2
    have himageNe : (C.image (nearXYLabel s)).Nonempty := Finset.image_nonempty.mpr hCne
    refine ⟨himageNe, ?_, ?_⟩
    · intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      have hmass := nearXY_mass_lower_bound s S (hCvalid S hS).2 h.1
      have hTne := finset_nonempty_of_positive_mass b (nearXYLabel s S) hmass
      have hTcenter : ∀ y ∈ nearXYLabel s S,
          dist center (s.right y) < radius b := by
        intro y hy
        obtain ⟨x, hxS, hxy⟩ := (Finset.mem_filter.mp hy).2
        have hxC : x ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S, hS, hxS⟩
        calc
          dist center (s.right y) ≤ dist center (s.left x) + dist (s.left x) (s.right y) :=
            dist_triangle _ _ _
          _ < radius a + δ := by
            apply add_lt_add (hcenter x hxC)
            simpa [dist_comm] using hxy
          _ ≤ radius b := h.2
      exact ⟨⟨hTne, center, hTcenter⟩, hmass⟩
    · have htargetValid : ∀ T ∈ C.image (nearXYLabel s),
          T ∈ openCech s.right (radius b) ∧
            mass b ≤ (T.card : ℝ) / Fintype.card Y := by
        intro T hT
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
        have hmass := nearXY_mass_lower_bound s S (hCvalid S hS).2 h.1
        have hTne := finset_nonempty_of_positive_mass b (nearXYLabel s S) hmass
        have hTcenter : ∀ y ∈ nearXYLabel s S,
            dist center (s.right y) < radius b := by
          intro y hy
          obtain ⟨x, hxS, hxy⟩ := (Finset.mem_filter.mp hy).2
          have hxC : x ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S, hS, hxS⟩
          calc
            dist center (s.right y) ≤ dist center (s.left x) + dist (s.left x) (s.right y) :=
              dist_triangle _ _ _
            _ < radius a + δ := by
              apply add_lt_add (hcenter x hxC)
              simpa [dist_comm] using hxy
            _ ≤ radius b := h.2
        exact ⟨⟨hTne, center, hTcenter⟩, hmass⟩
      have hUnionNe : ((C.image (nearXYLabel s)).biUnion id).Nonempty := by
        obtain ⟨T, hT⟩ := himageNe
        obtain ⟨y, hy⟩ := (htargetValid T hT).1.1
        exact ⟨y, Finset.mem_biUnion.mpr ⟨T, hT, hy⟩⟩
      refine ⟨hUnionNe, center, ?_⟩
      intro y hy
      obtain ⟨T, hT, hyT⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨x, hxS, hxy⟩ := (Finset.mem_filter.mp hyT).2
      have hxC : x ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S, hS, hxS⟩
      calc
        dist center (s.right y) ≤ dist center (s.left x) + dist (s.left x) (s.right y) :=
          dist_triangle _ _ _
        _ < radius a + δ := by
          apply add_lt_add (hcenter x hxC)
          simpa [dist_comm] using hxy
        _ ≤ radius b := h.2

private noncomputable def nearYXVertexMap {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (a b : Index)
    (h : mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b) :
    VertexMap (TDA.Topology.nerve (largeFaceCover s.right a))
      (TDA.Topology.nerve (largeFaceCover s.left b)) where
  toFun := nearYXLabel s
  map_face := by
    classical
    letI : DecidableEq (Finset X) := Classical.decEq _
    intro C hC
    obtain ⟨hCne, hCvalid, hCcenter⟩ := (mem_largeFaceNerve_iff s.right a C).mp hC
    obtain ⟨_, center, hcenter⟩ := hCcenter
    change C.image (nearYXLabel s) ∈ TDA.Topology.nerve (largeFaceCover s.left b)
    apply (mem_largeFaceNerve_iff s.left b _).2
    have himageNe : (C.image (nearYXLabel s)).Nonempty := Finset.image_nonempty.mpr hCne
    refine ⟨himageNe, ?_, ?_⟩
    · intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      have hmass := nearYX_mass_lower_bound s S (hCvalid S hS).2 h.1
      have hTne := finset_nonempty_of_positive_mass b (nearYXLabel s S) hmass
      have hTcenter : ∀ x ∈ nearYXLabel s S,
          dist center (s.left x) < radius b := by
        intro x hx
        obtain ⟨y, hyS, hxy⟩ := (Finset.mem_filter.mp hx).2
        have hyC : y ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S, hS, hyS⟩
        calc
          dist center (s.left x) ≤ dist center (s.right y) + dist (s.right y) (s.left x) :=
            dist_triangle _ _ _
          _ < radius a + δ := by
            apply add_lt_add (hcenter y hyC)
            simpa [dist_comm] using hxy
          _ ≤ radius b := h.2
      exact ⟨⟨hTne, center, hTcenter⟩, hmass⟩
    · have htargetValid : ∀ T ∈ C.image (nearYXLabel s),
          T ∈ openCech s.left (radius b) ∧
            mass b ≤ (T.card : ℝ) / Fintype.card X := by
        intro T hT
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
        have hmass := nearYX_mass_lower_bound s S (hCvalid S hS).2 h.1
        have hTne := finset_nonempty_of_positive_mass b (nearYXLabel s S) hmass
        have hTcenter : ∀ x ∈ nearYXLabel s S,
            dist center (s.left x) < radius b := by
          intro x hx
          obtain ⟨y, hyS, hxy⟩ := (Finset.mem_filter.mp hx).2
          have hyC : y ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S, hS, hyS⟩
          calc
            dist center (s.left x) ≤ dist center (s.right y) + dist (s.right y) (s.left x) :=
              dist_triangle _ _ _
            _ < radius a + δ := by
              apply add_lt_add (hcenter y hyC)
              simpa [dist_comm] using hxy
            _ ≤ radius b := h.2
        exact ⟨⟨hTne, center, hTcenter⟩, hmass⟩
      have hUnionNe : ((C.image (nearYXLabel s)).biUnion id).Nonempty := by
        obtain ⟨T, hT⟩ := himageNe
        obtain ⟨x, hx⟩ := (htargetValid T hT).1.1
        exact ⟨x, Finset.mem_biUnion.mpr ⟨T, hT, hx⟩⟩
      refine ⟨hUnionNe, center, ?_⟩
      intro x hx
      obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨y, hyS, hxy⟩ := (Finset.mem_filter.mp hxT).2
      have hyC : y ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S, hS, hyS⟩
      calc
        dist center (s.left x) ≤ dist center (s.right y) + dist (s.right y) (s.left x) :=
          dist_triangle _ _ _
        _ < radius a + δ := by
          apply add_lt_add (hcenter y hyC)
          simpa [dist_comm] using hxy
        _ ≤ radius b := h.2

private theorem nearXY_nearYX_contiguous {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) {a b c : Index}
    (hab : mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b)
    (hbc : mass c + δ ≤ mass b ∧ radius b + δ ≤ radius c)
    (hac : TDA.Topology.nerve (largeFaceCover s.left a) ≤
      TDA.Topology.nerve (largeFaceCover s.left c)) :
    TDA.Simplicial.Contiguous
      (VertexMap.comp (nearXYVertexMap s a b hab) (nearYXVertexMap s b c hbc))
      (inclusionVertexMap hac) := by
  classical
  letI : DecidableEq (Finset X) := Classical.decEq _
  intro C hC
  obtain ⟨hCne, hCvalid, hCcenter⟩ := (mem_largeFaceNerve_iff s.left a C).mp hC
  obtain ⟨_, center, hcenter⟩ := hCcenter
  have hmassAC : mass c ≤ mass a :=
    (le_add_of_nonneg_right δ.coe_nonneg).trans
      (hbc.1.trans ((le_add_of_nonneg_right δ.coe_nonneg).trans hab.1))
  have hradiusAC : radius a ≤ radius c :=
    (le_add_of_nonneg_right δ.coe_nonneg).trans
      (hab.2.trans ((le_add_of_nonneg_right δ.coe_nonneg).trans hbc.2))
  let doubleNear (S : Finset X) := nearYXLabel s (nearXYLabel s S)
  let labels := C ∪ C.image doubleNear
  have hlabels : labels ∈ TDA.Topology.nerve (largeFaceCover s.left c) := by
    apply (mem_largeFaceNerve_iff s.left c labels).2
    have hvalid : ∀ S ∈ labels, S ∈ openCech s.left (radius c) ∧
        mass c ≤ (S.card : ℝ) / Fintype.card X := by
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · have hlarge := (hCvalid S hS).2
        have hne := (hCvalid S hS).1.1
        have hcenterS : ∀ x ∈ S, dist center (s.left x) < radius c := by
          intro x hx
          exact (hcenter x (Finset.mem_biUnion.mpr ⟨S, hS, hx⟩)).trans_le hradiusAC
        exact ⟨⟨hne, center, hcenterS⟩, hmassAC.trans hlarge⟩
      · obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_image.mp hS
        have hmid := nearXY_mass_lower_bound s S₀ (hCvalid S₀ hS₀).2 hab.1
        have hfinal := nearYX_mass_lower_bound s (nearXYLabel s S₀) hmid hbc.1
        have hfinalNe := finset_nonempty_of_positive_mass c (doubleNear S₀) hfinal
        have hcenterFinal : ∀ x ∈ doubleNear S₀, dist center (s.left x) < radius c := by
          intro x hx
          obtain ⟨y, hy, hxy⟩ := (Finset.mem_filter.mp hx).2
          obtain ⟨x₀, hx₀, hyx₀⟩ := (Finset.mem_filter.mp hy).2
          have hx₀C : x₀ ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S₀, hS₀, hx₀⟩
          calc
            dist center (s.left x) ≤ dist center (s.right y) + dist (s.right y) (s.left x) :=
              dist_triangle _ _ _
            _ ≤ (dist center (s.left x₀) + dist (s.left x₀) (s.right y)) +
                dist (s.right y) (s.left x) := by
              exact add_le_add (dist_triangle _ _ _) le_rfl
            _ < radius a + δ + δ := by
              have h₁ : dist center (s.left x₀) < radius a := by
                simpa only [Metric.mem_ball] using hcenter x₀ hx₀C
              have h₂ : dist (s.left x₀) (s.right y) < (δ : ℝ) := by
                simpa [dist_comm] using hyx₀
              have h₃ : dist (s.right y) (s.left x) < (δ : ℝ) := by
                simpa [dist_comm] using hxy
              linarith
            _ ≤ radius c := by
              have hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
              linarith
        exact ⟨⟨hfinalNe, center, hcenterFinal⟩, hfinal⟩
    have hlabelsNe : labels.Nonempty := by
      obtain ⟨S, hS⟩ := hCne
      exact ⟨S, Finset.mem_union_left _ hS⟩
    have hlabelsUnionNe : (labels.biUnion id).Nonempty := by
      obtain ⟨S, hS⟩ := hCne
      obtain ⟨x, hx⟩ := (hCvalid S hS).1.1
      exact ⟨x, Finset.mem_biUnion.mpr ⟨S, Finset.mem_union_left _ hS, hx⟩⟩
    refine ⟨hlabelsNe, hvalid, ⟨hlabelsUnionNe, center, ?_⟩⟩
    intro x hx
    obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
    rcases Finset.mem_union.mp hS with hS | hS
    · have hxC : x ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S, hS, hxS⟩
      exact (hcenter x hxC).trans_le hradiusAC
    · obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_image.mp hS
      have hmid := nearXY_mass_lower_bound s S₀ (hCvalid S₀ hS₀).2 hab.1
      have hfinal := nearYX_mass_lower_bound s (nearXYLabel s S₀) hmid hbc.1
      have hfinalNe := finset_nonempty_of_positive_mass c (doubleNear S₀) hfinal
      have hcenterFinal : ∀ x ∈ doubleNear S₀, dist center (s.left x) < radius c := by
        intro x hx'
        obtain ⟨y, hy, hxy⟩ := (Finset.mem_filter.mp hx').2
        obtain ⟨x₀, hx₀, hyx₀⟩ := (Finset.mem_filter.mp hy).2
        have hx₀C : x₀ ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨S₀, hS₀, hx₀⟩
        calc
          dist center (s.left x) ≤ dist center (s.right y) + dist (s.right y) (s.left x) :=
            dist_triangle _ _ _
          _ ≤ (dist center (s.left x₀) + dist (s.left x₀) (s.right y)) +
                dist (s.right y) (s.left x) := by
              exact add_le_add (dist_triangle _ _ _) le_rfl
          _ < radius a + δ + δ := by
              have h₁ : dist center (s.left x₀) < radius a := by
                simpa only [Metric.mem_ball] using hcenter x₀ hx₀C
              have h₂ : dist (s.left x₀) (s.right y) < (δ : ℝ) := by
                simpa [dist_comm] using hyx₀
              have h₃ : dist (s.right y) (s.left x) < (δ : ℝ) := by
                simpa [dist_comm] using hxy
              linarith
          _ ≤ radius c := by
              have hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
              linarith
      exact hcenterFinal x hxS
  change C.image
      (VertexMap.comp (nearXYVertexMap s a b hab) (nearYXVertexMap s b c hbc)).toFun ∪
      C.image (inclusionVertexMap hac).toFun ∈
    TDA.Topology.nerve (largeFaceCover s.left c)
  simpa [labels, doubleNear, VertexMap.comp, Function.comp_def,
    nearXYVertexMap, nearYXVertexMap, inclusionVertexMap, Finset.union_comm] using hlabels

private theorem nearYX_nearXY_contiguous {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) {a b c : Index}
    (hab : mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b)
    (hbc : mass c + δ ≤ mass b ∧ radius b + δ ≤ radius c)
    (hac : TDA.Topology.nerve (largeFaceCover s.right a) ≤
      TDA.Topology.nerve (largeFaceCover s.right c)) :
    TDA.Simplicial.Contiguous
      (VertexMap.comp (nearYXVertexMap s a b hab) (nearXYVertexMap s b c hbc))
      (inclusionVertexMap hac) := by
  classical
  letI : DecidableEq (Finset Y) := Classical.decEq _
  intro C hC
  obtain ⟨hCne, hCvalid, hCcenter⟩ := (mem_largeFaceNerve_iff s.right a C).mp hC
  obtain ⟨_, center, hcenter⟩ := hCcenter
  have hmassAC : mass c ≤ mass a :=
    (le_add_of_nonneg_right δ.coe_nonneg).trans
      (hbc.1.trans ((le_add_of_nonneg_right δ.coe_nonneg).trans hab.1))
  have hradiusAC : radius a ≤ radius c :=
    (le_add_of_nonneg_right δ.coe_nonneg).trans
      (hab.2.trans ((le_add_of_nonneg_right δ.coe_nonneg).trans hbc.2))
  let doubleNear (T : Finset Y) := nearXYLabel s (nearYXLabel s T)
  let labels := C ∪ C.image doubleNear
  have hlabels : labels ∈ TDA.Topology.nerve (largeFaceCover s.right c) := by
    apply (mem_largeFaceNerve_iff s.right c labels).2
    have hvalid : ∀ T ∈ labels, T ∈ openCech s.right (radius c) ∧
        mass c ≤ (T.card : ℝ) / Fintype.card Y := by
      intro T hT
      rcases Finset.mem_union.mp hT with hT | hT
      · have hlarge := (hCvalid T hT).2
        have hne := (hCvalid T hT).1.1
        have hcenterT : ∀ y ∈ T, dist center (s.right y) < radius c := by
          intro y hy
          exact (hcenter y (Finset.mem_biUnion.mpr ⟨T, hT, hy⟩)).trans_le hradiusAC
        exact ⟨⟨hne, center, hcenterT⟩, hmassAC.trans hlarge⟩
      · obtain ⟨T₀, hT₀, rfl⟩ := Finset.mem_image.mp hT
        have hmid := nearYX_mass_lower_bound s T₀ (hCvalid T₀ hT₀).2 hab.1
        have hfinal := nearXY_mass_lower_bound s (nearYXLabel s T₀) hmid hbc.1
        have hfinalNe := finset_nonempty_of_positive_mass c (doubleNear T₀) hfinal
        have hcenterFinal : ∀ y ∈ doubleNear T₀, dist center (s.right y) < radius c := by
          intro y hy
          obtain ⟨x, hx, hyx⟩ := (Finset.mem_filter.mp hy).2
          obtain ⟨y₀, hy₀, hxy₀⟩ := (Finset.mem_filter.mp hx).2
          have hy₀C : y₀ ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨T₀, hT₀, hy₀⟩
          calc
            dist center (s.right y) ≤ dist center (s.left x) + dist (s.left x) (s.right y) :=
              dist_triangle _ _ _
            _ ≤ (dist center (s.right y₀) + dist (s.right y₀) (s.left x)) +
                dist (s.left x) (s.right y) := by
              exact add_le_add (dist_triangle _ _ _) le_rfl
            _ < radius a + δ + δ := by
              have h₁ : dist center (s.right y₀) < radius a := by
                simpa only [Metric.mem_ball] using hcenter y₀ hy₀C
              have h₂ : dist (s.right y₀) (s.left x) < (δ : ℝ) := by
                simpa [dist_comm] using hxy₀
              have h₃ : dist (s.left x) (s.right y) < (δ : ℝ) := by
                simpa [dist_comm] using hyx
              linarith
            _ ≤ radius c := by
              have hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
              linarith
        exact ⟨⟨hfinalNe, center, hcenterFinal⟩, hfinal⟩
    have hlabelsNe : labels.Nonempty := by
      obtain ⟨T, hT⟩ := hCne
      exact ⟨T, Finset.mem_union_left _ hT⟩
    have hlabelsUnionNe : (labels.biUnion id).Nonempty := by
      obtain ⟨T, hT⟩ := hCne
      obtain ⟨y, hy⟩ := (hCvalid T hT).1.1
      exact ⟨y, Finset.mem_biUnion.mpr ⟨T, Finset.mem_union_left _ hT, hy⟩⟩
    refine ⟨hlabelsNe, hvalid, ⟨hlabelsUnionNe, center, ?_⟩⟩
    intro y hy
    obtain ⟨T, hT, hyT⟩ := Finset.mem_biUnion.mp hy
    rcases Finset.mem_union.mp hT with hT | hT
    · have hyC : y ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨T, hT, hyT⟩
      exact (hcenter y hyC).trans_le hradiusAC
    · obtain ⟨T₀, hT₀, rfl⟩ := Finset.mem_image.mp hT
      have hmid := nearYX_mass_lower_bound s T₀ (hCvalid T₀ hT₀).2 hab.1
      have hfinal := nearXY_mass_lower_bound s (nearYXLabel s T₀) hmid hbc.1
      have hfinalNe := finset_nonempty_of_positive_mass c (doubleNear T₀) hfinal
      have hcenterFinal : ∀ y ∈ doubleNear T₀, dist center (s.right y) < radius c := by
        intro y hy'
        obtain ⟨x, hx, hyx⟩ := (Finset.mem_filter.mp hy').2
        obtain ⟨y₀, hy₀, hxy₀⟩ := (Finset.mem_filter.mp hx).2
        have hy₀C : y₀ ∈ C.biUnion id := Finset.mem_biUnion.mpr ⟨T₀, hT₀, hy₀⟩
        calc
          dist center (s.right y) ≤ dist center (s.left x) + dist (s.left x) (s.right y) :=
            dist_triangle _ _ _
          _ ≤ (dist center (s.right y₀) + dist (s.right y₀) (s.left x)) +
                dist (s.left x) (s.right y) := by
              exact add_le_add (dist_triangle _ _ _) le_rfl
          _ < radius a + δ + δ := by
              have h₁ : dist center (s.right y₀) < radius a := by
                simpa only [Metric.mem_ball] using hcenter y₀ hy₀C
              have h₂ : dist (s.right y₀) (s.left x) < (δ : ℝ) := by
                simpa [dist_comm] using hxy₀
              have h₃ : dist (s.left x) (s.right y) < (δ : ℝ) := by
                simpa [dist_comm] using hyx
              linarith
          _ ≤ radius c := by
              have hδ : 0 ≤ (δ : ℝ) := δ.coe_nonneg
              linarith
      exact hcenterFinal y hyT
  change C.image
      (VertexMap.comp (nearYXVertexMap s a b hab) (nearXYVertexMap s b c hbc)).toFun ∪
      C.image (inclusionVertexMap hac).toFun ∈
    TDA.Topology.nerve (largeFaceCover s.right c)
  simpa [labels, doubleNear, VertexMap.comp, Function.comp_def,
    nearXYVertexMap, nearYXVertexMap, inclusionVertexMap, Finset.union_comm] using hlabels

/-- The concrete homology module over the restricted two-copy index. Same-side
arrows use large-face filtration inclusions; cross-side arrows use the
near-label maps induced by the finite sup-norm witness. -/
noncomputable def SupNormWitness.largeFaceNerveHomologyInterleaving {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    PModule.{w, 0, max u w} R (InterleavingIndex δ) where
  obj i :=
    if h : i.side then
      ModuleCat.of R (simplicialHomology (largeFaceNerveBifiltration s.right i.point) R n)
    else
      ModuleCat.of R (simplicialHomology (largeFaceNerveBifiltration s.left i.point) R n)
  map := by
    intro i j f
    rcases i with ⟨a, ba⟩
    rcases j with ⟨b, bb⟩
    have hij := leOfHom f
    cases ba <;> cases bb
    all_goals
      simp only [interleavingIndex_le_iff, penalty, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte, add_zero] at hij
    · change mass b ≤ mass a ∧ radius a ≤ radius b at hij
      exact simplicialHomologyIncl R
        ((largeFaceNerveBifiltration s.left).monotone hij) n
    · change mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b at hij
      exact simplicialHomologyMap R (nearXYVertexMap s a b hij) n
    · change mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b at hij
      exact simplicialHomologyMap R (nearYXVertexMap s a b hij) n
    · change mass b ≤ mass a ∧ radius a ≤ radius b at hij
      exact simplicialHomologyIncl R
        ((largeFaceNerveBifiltration s.right).monotone hij) n
  map_id := by
    intro i
    rcases i with ⟨a, b⟩
    cases b
    · change simplicialHomologyIncl R
        ((largeFaceNerveBifiltration s.left).monotone (leOfHom (𝟙 a))) n = 𝟙 _
      have hinc : (largeFaceNerveBifiltration s.left).monotone
          (leOfHom (𝟙 a)) = le_refl (largeFaceNerveBifiltration s.left a) :=
        Subsingleton.elim _ _
      rw [hinc]
      exact simplicialHomologyIncl_id R (largeFaceNerveBifiltration s.left a) n
    · change simplicialHomologyIncl R
        ((largeFaceNerveBifiltration s.right).monotone (leOfHom (𝟙 a))) n = 𝟙 _
      have hinc : (largeFaceNerveBifiltration s.right).monotone
          (leOfHom (𝟙 a)) = le_refl (largeFaceNerveBifiltration s.right a) :=
        Subsingleton.elim _ _
      rw [hinc]
      exact simplicialHomologyIncl_id R (largeFaceNerveBifiltration s.right a) n
  map_comp := by
    intro i j k f g
    rcases i with ⟨a, ba⟩
    rcases j with ⟨b, bb⟩
    rcases k with ⟨c, bc⟩
    have hij := leOfHom f
    have hjk := leOfHom g
    have hik := leOfHom (f ≫ g)
    cases ba <;> cases bb <;> cases bc
    all_goals
      simp only [interleavingIndex_le_iff, penalty, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte, add_zero] at hij hjk hik
    · change mass b ≤ mass a ∧ radius a ≤ radius b at hij
      change mass c ≤ mass b ∧ radius b ≤ radius c at hjk
      change mass c ≤ mass a ∧ radius a ≤ radius c at hik
      change simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.left).monotone hik) n =
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.left).monotone hij) n ≫
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.left).monotone hjk) n
      exact simplicialHomologyIncl_comp R
        ((largeFaceNerveBifiltration s.left).monotone hij)
        ((largeFaceNerveBifiltration s.left).monotone hjk) n
    · change mass b ≤ mass a ∧ radius a ≤ radius b at hij
      change mass c + δ ≤ mass b ∧ radius b + δ ≤ radius c at hjk
      change mass c + δ ≤ mass a ∧ radius a + δ ≤ radius c at hik
      change simplicialHomologyMap R (nearXYVertexMap s a c hik) n =
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.left).monotone hij) n ≫
        simplicialHomologyMap R (nearXYVertexMap s b c hjk) n
      let hleft := (largeFaceNerveBifiltration s.left).monotone hij
      have hvertex : VertexMap.comp (inclusionVertexMap hleft)
          (nearXYVertexMap s b c hjk) = nearXYVertexMap s a c hik := by
        apply VertexMap.ext
        intro S
        rfl
      have hcomp : simplicialHomologyMap R
          (VertexMap.comp (inclusionVertexMap hleft) (nearXYVertexMap s b c hjk)) n =
          simplicialHomologyMap R (inclusionVertexMap hleft) n ≫
            simplicialHomologyMap R (nearXYVertexMap s b c hjk) n :=
        simplicialHomologyMap_comp R (inclusionVertexMap hleft)
          (nearXYVertexMap s b c hjk) n
      have hdirect : simplicialHomologyMap R (nearXYVertexMap s a c hik) n =
          simplicialHomologyMap R
            (VertexMap.comp (inclusionVertexMap hleft) (nearXYVertexMap s b c hjk)) n :=
        congrArg (fun f => simplicialHomologyMap R f n) hvertex.symm
      have hinc : simplicialHomologyMap R (inclusionVertexMap hleft) n ≫
          simplicialHomologyMap R (nearXYVertexMap s b c hjk) n =
          simplicialHomologyIncl R hleft n ≫
            simplicialHomologyMap R (nearXYVertexMap s b c hjk) n :=
        congrArg (fun f => f ≫ simplicialHomologyMap R (nearXYVertexMap s b c hjk) n)
          (simplicialHomologyMap_inclusion R hleft n)
      have hchain : simplicialHomologyMap R (nearXYVertexMap s a c hik) n =
          simplicialHomologyIncl R hleft n ≫
            simplicialHomologyMap R (nearXYVertexMap s b c hjk) n :=
        hdirect.trans (hcomp.trans hinc)
      exact hchain
    · change mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b at hij
      change mass c + δ ≤ mass b ∧ radius b + δ ≤ radius c at hjk
      change mass c ≤ mass a ∧ radius a ≤ radius c at hik
      change simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.left).monotone hik) n =
        simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
        simplicialHomologyMap R (nearYXVertexMap s b c hjk) n
      let hleft := (largeFaceNerveBifiltration s.left).monotone hik
      have hcontig := TDA.Simplicial.Contiguous.simplicialHomologyMap_eq R
        (nearXY_nearYX_contiguous s (a := a) (b := b) (c := c) hij hjk hleft) n
      have hinc : simplicialHomologyIncl R hleft n =
          simplicialHomologyMap R (inclusionVertexMap hleft) n :=
        (simplicialHomologyMap_inclusion R hleft n).symm
      have hcomp : simplicialHomologyMap R
          (VertexMap.comp (nearXYVertexMap s a b hij) (nearYXVertexMap s b c hjk)) n =
          simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
            simplicialHomologyMap R (nearYXVertexMap s b c hjk) n :=
        simplicialHomologyMap_comp R (nearXYVertexMap s a b hij)
          (nearYXVertexMap s b c hjk) n
      have hchain : simplicialHomologyIncl R hleft n =
          simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
            simplicialHomologyMap R (nearYXVertexMap s b c hjk) n :=
        hinc.trans (hcontig.symm.trans hcomp)
      exact hchain
    · change mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b at hij
      change mass c ≤ mass b ∧ radius b ≤ radius c at hjk
      change mass c + δ ≤ mass a ∧ radius a + δ ≤ radius c at hik
      change simplicialHomologyMap R (nearXYVertexMap s a c hik) n =
        simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.right).monotone hjk) n
      let hright := (largeFaceNerveBifiltration s.right).monotone hjk
      have hvertex : VertexMap.comp (nearXYVertexMap s a b hij)
          (inclusionVertexMap hright) = nearXYVertexMap s a c hik := by
        apply VertexMap.ext
        intro S
        rfl
      have hcomp : simplicialHomologyMap R
          (VertexMap.comp (nearXYVertexMap s a b hij) (inclusionVertexMap hright)) n =
          simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
            simplicialHomologyMap R (inclusionVertexMap hright) n :=
        simplicialHomologyMap_comp R (nearXYVertexMap s a b hij)
          (inclusionVertexMap hright) n
      have hdirect : simplicialHomologyMap R (nearXYVertexMap s a c hik) n =
          simplicialHomologyMap R
            (VertexMap.comp (nearXYVertexMap s a b hij) (inclusionVertexMap hright)) n :=
        congrArg (fun f => simplicialHomologyMap R f n) hvertex.symm
      have hinc : simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
          simplicialHomologyMap R (inclusionVertexMap hright) n =
          simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
            simplicialHomologyIncl R hright n :=
        congrArg (fun f => simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫ f)
          (simplicialHomologyMap_inclusion R hright n)
      have hchain : simplicialHomologyMap R (nearXYVertexMap s a c hik) n =
          simplicialHomologyMap R (nearXYVertexMap s a b hij) n ≫
            simplicialHomologyIncl R hright n :=
        hdirect.trans (hcomp.trans hinc)
      exact hchain
    · change mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b at hij
      change mass c ≤ mass b ∧ radius b ≤ radius c at hjk
      change mass c + δ ≤ mass a ∧ radius a + δ ≤ radius c at hik
      change simplicialHomologyMap R (nearYXVertexMap s a c hik) n =
        simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.left).monotone hjk) n
      let hleft := (largeFaceNerveBifiltration s.left).monotone hjk
      have hvertex : VertexMap.comp (nearYXVertexMap s a b hij)
          (inclusionVertexMap hleft) = nearYXVertexMap s a c hik := by
        apply VertexMap.ext
        intro T
        rfl
      have hcomp : simplicialHomologyMap R
          (VertexMap.comp (nearYXVertexMap s a b hij) (inclusionVertexMap hleft)) n =
          simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
            simplicialHomologyMap R (inclusionVertexMap hleft) n :=
        simplicialHomologyMap_comp R (nearYXVertexMap s a b hij)
          (inclusionVertexMap hleft) n
      have hdirect : simplicialHomologyMap R (nearYXVertexMap s a c hik) n =
          simplicialHomologyMap R
            (VertexMap.comp (nearYXVertexMap s a b hij) (inclusionVertexMap hleft)) n :=
        congrArg (fun f => simplicialHomologyMap R f n) hvertex.symm
      have hinc : simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
          simplicialHomologyMap R (inclusionVertexMap hleft) n =
          simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
            simplicialHomologyIncl R hleft n :=
        congrArg (fun f => simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫ f)
          (simplicialHomologyMap_inclusion R hleft n)
      have hchain : simplicialHomologyMap R (nearYXVertexMap s a c hik) n =
          simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
            simplicialHomologyIncl R hleft n :=
        hdirect.trans (hcomp.trans hinc)
      exact hchain
    · change mass b + δ ≤ mass a ∧ radius a + δ ≤ radius b at hij
      change mass c + δ ≤ mass b ∧ radius b + δ ≤ radius c at hjk
      change mass c ≤ mass a ∧ radius a ≤ radius c at hik
      change simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.right).monotone hik) n =
        simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
        simplicialHomologyMap R (nearXYVertexMap s b c hjk) n
      let hright := (largeFaceNerveBifiltration s.right).monotone hik
      have hcontig := TDA.Simplicial.Contiguous.simplicialHomologyMap_eq R
        (nearYX_nearXY_contiguous s (a := a) (b := b) (c := c) hij hjk hright) n
      have hinc : simplicialHomologyIncl R hright n =
          simplicialHomologyMap R (inclusionVertexMap hright) n :=
        (simplicialHomologyMap_inclusion R hright n).symm
      have hcomp : simplicialHomologyMap R
          (VertexMap.comp (nearYXVertexMap s a b hij) (nearXYVertexMap s b c hjk)) n =
          simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
            simplicialHomologyMap R (nearXYVertexMap s b c hjk) n :=
        simplicialHomologyMap_comp R (nearYXVertexMap s a b hij)
          (nearXYVertexMap s b c hjk) n
      have hchain : simplicialHomologyIncl R hright n =
          simplicialHomologyMap R (nearYXVertexMap s a b hij) n ≫
            simplicialHomologyMap R (nearXYVertexMap s b c hjk) n :=
        hinc.trans (hcontig.symm.trans hcomp)
      exact hchain
    · change mass b ≤ mass a ∧ radius a ≤ radius b at hij
      change mass c + δ ≤ mass b ∧ radius b + δ ≤ radius c at hjk
      change mass c + δ ≤ mass a ∧ radius a + δ ≤ radius c at hik
      change simplicialHomologyMap R (nearYXVertexMap s a c hik) n =
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.right).monotone hij) n ≫
        simplicialHomologyMap R (nearYXVertexMap s b c hjk) n
      let hright := (largeFaceNerveBifiltration s.right).monotone hij
      have hvertex : VertexMap.comp (inclusionVertexMap hright)
          (nearYXVertexMap s b c hjk) = nearYXVertexMap s a c hik := by
        apply VertexMap.ext
        intro T
        rfl
      have hcomp : simplicialHomologyMap R
          (VertexMap.comp (inclusionVertexMap hright) (nearYXVertexMap s b c hjk)) n =
          simplicialHomologyMap R (inclusionVertexMap hright) n ≫
            simplicialHomologyMap R (nearYXVertexMap s b c hjk) n :=
        simplicialHomologyMap_comp R (inclusionVertexMap hright)
          (nearYXVertexMap s b c hjk) n
      have hdirect : simplicialHomologyMap R (nearYXVertexMap s a c hik) n =
          simplicialHomologyMap R
            (VertexMap.comp (inclusionVertexMap hright) (nearYXVertexMap s b c hjk)) n :=
        congrArg (fun f => simplicialHomologyMap R f n) hvertex.symm
      have hinc : simplicialHomologyMap R (inclusionVertexMap hright) n ≫
          simplicialHomologyMap R (nearYXVertexMap s b c hjk) n =
          simplicialHomologyIncl R hright n ≫
            simplicialHomologyMap R (nearYXVertexMap s b c hjk) n :=
        congrArg (fun f => f ≫ simplicialHomologyMap R (nearYXVertexMap s b c hjk) n)
          (simplicialHomologyMap_inclusion R hright n)
      have hchain : simplicialHomologyMap R (nearYXVertexMap s a c hik) n =
          simplicialHomologyIncl R hright n ≫
            simplicialHomologyMap R (nearYXVertexMap s b c hjk) n :=
        hdirect.trans (hcomp.trans hinc)
      exact hchain
    · change mass b ≤ mass a ∧ radius a ≤ radius b at hij
      change mass c ≤ mass b ∧ radius b ≤ radius c at hjk
      change mass c ≤ mass a ∧ radius a ≤ radius c at hik
      change simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.right).monotone hik) n =
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.right).monotone hij) n ≫
        simplicialHomologyIncl R
          ((largeFaceNerveBifiltration s.right).monotone hjk) n
      exact simplicialHomologyIncl_comp R
        ((largeFaceNerveBifiltration s.right).monotone hij)
        ((largeFaceNerveBifiltration s.right).monotone hjk) n

/-- Restricting the two-copy homology module to the first copy recovers the
large-face nerve homology bifiltration on the first finite metric sample. -/
theorem SupNormWitness.largeFaceNerveHomologyInterleaving_left {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    (copy δ false).toFunctor ⋙ s.largeFaceNerveHomologyInterleaving R n =
      simplicialHomologyPModule R (largeFaceNerveBifiltration s.left) n := by
  rfl

/-- Restricting the two-copy homology module to the second copy recovers the
large-face nerve homology bifiltration on the second finite metric sample. -/
theorem SupNormWitness.largeFaceNerveHomologyInterleaving_right {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    (copy δ true).toFunctor ⋙ s.largeFaceNerveHomologyInterleaving R n =
      simplicialHomologyPModule R (largeFaceNerveBifiltration s.right) n := by
  rfl

private noncomputable def SupNormWitness.homologyInterleavingObj {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ)
    (i : InterleavingIndex δ) : ModuleCat.{max u w} R :=
  if hi : i.side then
    (homology R (inferInstance : MetricSpace Y) n).obj i.point
  else
    (homology R (inferInstance : MetricSpace X) n).obj i.point

private noncomputable def SupNormWitness.homologyInterleavingIsoAt {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ)
    (i : InterleavingIndex δ) :
    s.homologyInterleavingObj R n i ≅
      (s.largeFaceNerveHomologyInterleaving R n).obj i := by
  rcases i with ⟨a, side⟩
  cases side
  · exact (ripsHomologyToLargeFaceNerveIso R (inferInstance : MetricSpace X)
      s.left (fun x x' => (s.left_isometry.dist_eq x x').symm) n).app a
  · exact (ripsHomologyToLargeFaceNerveIso R (inferInstance : MetricSpace Y)
      s.right (fun y y' => (s.right_isometry.dist_eq y y').symm) n).app a

/-- The finite GP witness interleaves the actual normalized subdivision-Rips
homology modules over the restricted positive two-copy index. The definition
transports the verified large-face nerve diagram along the natural Čech/Rips
and large-face nerve comparisons. -/
noncomputable def SupNormWitness.homologyInterleaving {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    PModule.{w, 0, max u w} R (InterleavingIndex δ) where
  obj i := s.homologyInterleavingObj R n i
  map {i j} f :=
    (s.homologyInterleavingIsoAt R n i).hom ≫
      (s.largeFaceNerveHomologyInterleaving R n).map f ≫
      (s.homologyInterleavingIsoAt R n j).inv
  map_id := by
    intro i
    simp [Category.assoc]
  map_comp := by
    intro i j k f g
    simp [Category.assoc]

/-- The left restriction of the transported interleaving is exactly the
actual normalized subdivision-Rips homology module. -/
theorem SupNormWitness.homologyInterleaving_left {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    (copy δ false).toFunctor ⋙ s.homologyInterleaving R n =
      homology R (inferInstance : MetricSpace X) n := by
  refine CategoryTheory.Functor.ext (h_obj := fun a => by
    dsimp [Functor.comp_obj, SupNormWitness.homologyInterleaving,
      SupNormWitness.homologyInterleavingObj, copy]
    change (homology R (inferInstance : MetricSpace X) n).obj
      ((copy δ false).toFun a).point = (homology R (inferInstance : MetricSpace X) n).obj a
    rfl) ?_
  intro a b f
  let e := ripsHomologyToLargeFaceNerveIso R (inferInstance : MetricSpace X)
    s.left (fun x x' => (s.left_isometry.dist_eq x x').symm) n
  have hN : (s.largeFaceNerveHomologyInterleaving R n).map
      ((copy δ false).toFunctor.map f) =
      (simplicialHomologyPModule R (largeFaceNerveBifiltration s.left) n).map f := by
    change ((copy δ false).toFunctor ⋙
      s.largeFaceNerveHomologyInterleaving R n).map f = _
    rfl
  change (e.app a).hom ≫
      (s.largeFaceNerveHomologyInterleaving R n).map
        ((copy δ false).toFunctor.map f) ≫ (e.app b).inv =
    (homology R (inferInstance : MetricSpace X) n).map f
  rw [hN]
  have hnat' : (e.app a).hom ≫
      (simplicialHomologyPModule R (largeFaceNerveBifiltration s.left) n).map f =
      (homology R (inferInstance : MetricSpace X) n).map f ≫ (e.app b).hom := by
    change e.hom.app a ≫
        (simplicialHomologyPModule R (largeFaceNerveBifiltration s.left) n).map f =
      (homology R (inferInstance : MetricSpace X) n).map f ≫ e.hom.app b
    exact (e.hom.naturality f).symm
  calc
    (e.app a).hom ≫
        (simplicialHomologyPModule R (largeFaceNerveBifiltration s.left) n).map f ≫
        (e.app b).inv =
      ((homology R (inferInstance : MetricSpace X) n).map f ≫ (e.app b).hom) ≫
        (e.app b).inv := by rw [← Category.assoc, hnat']
    _ = (homology R (inferInstance : MetricSpace X) n).map f := by
      simp [Category.assoc]

/-- The right restriction of the transported interleaving is exactly the
actual normalized subdivision-Rips homology module. -/
theorem SupNormWitness.homologyInterleaving_right {δ : ℝ≥0}
    (s : SupNormWitness X Y δ) (R : Type w) [Ring R] (n : ℕ) :
    (copy δ true).toFunctor ⋙ s.homologyInterleaving R n =
      homology R (inferInstance : MetricSpace Y) n := by
  refine CategoryTheory.Functor.ext (h_obj := fun a => by
    dsimp [Functor.comp_obj, SupNormWitness.homologyInterleaving,
      SupNormWitness.homologyInterleavingObj, copy]
    change (homology R (inferInstance : MetricSpace Y) n).obj
      ((copy δ true).toFun a).point = (homology R (inferInstance : MetricSpace Y) n).obj a
    rfl) ?_
  intro a b f
  let e := ripsHomologyToLargeFaceNerveIso R (inferInstance : MetricSpace Y)
    s.right (fun y y' => (s.right_isometry.dist_eq y y').symm) n
  have hN : (s.largeFaceNerveHomologyInterleaving R n).map
      ((copy δ true).toFunctor.map f) =
      (simplicialHomologyPModule R (largeFaceNerveBifiltration s.right) n).map f := by
    change ((copy δ true).toFunctor ⋙
      s.largeFaceNerveHomologyInterleaving R n).map f = _
    rfl
  change (e.app a).hom ≫
      (s.largeFaceNerveHomologyInterleaving R n).map
        ((copy δ true).toFunctor.map f) ≫ (e.app b).inv =
    (homology R (inferInstance : MetricSpace Y) n).map f
  rw [hN]
  have hnat' : (e.app a).hom ≫
      (simplicialHomologyPModule R (largeFaceNerveBifiltration s.right) n).map f =
      (homology R (inferInstance : MetricSpace Y) n).map f ≫ (e.app b).hom := by
    change e.hom.app a ≫
        (simplicialHomologyPModule R (largeFaceNerveBifiltration s.right) n).map f =
      (homology R (inferInstance : MetricSpace Y) n).map f ≫ e.hom.app b
    exact (e.hom.naturality f).symm
  calc
    (e.app a).hom ≫
        (simplicialHomologyPModule R (largeFaceNerveBifiltration s.right) n).map f ≫
        (e.app b).inv =
      ((homology R (inferInstance : MetricSpace Y) n).map f ≫ (e.app b).hom) ≫
        (e.app b).inv := by rw [← Category.assoc, hnat']
    _ = (homology R (inferInstance : MetricSpace Y) n).map f := by
      simp [Category.assoc]

private def subdivisionRipsHomologyInterleavingExistsAt (δ : ℝ≥0)
    (d : MetricSpace X) (e : MetricSpace Y) (R : Type w) [Ring R] (n : ℕ) : Prop :=
  ∃ M : PModule.{w, 0, max u w} R (InterleavingIndex δ),
    (copy δ false).toFunctor ⋙ M = homology R d n ∧
    (copy δ true).toFunctor ⋙ M = homology R e n

/-- The infimum of all finite nonnegative scales admitting a restricted-index
interleaving of the actual normalized subdivision-Rips homology modules. -/
noncomputable def subdivisionRipsHomologyInterleavingDistance
    (d : MetricSpace X) (e : MetricSpace Y) (R : Type w) [Ring R] (n : ℕ) : ℝ≥0∞ := by
  classical
  exact ⨅ δ : ℝ≥0,
    if subdivisionRipsHomologyInterleavingExistsAt δ d e R n then (δ : ℝ≥0∞) else ∞

/-- Every finite normalized subdivision-Rips homology interleaving scale can be
chosen arbitrarily above the finite uniform Gromov-Prokhorov distance. -/
theorem subdivisionRipsHomologyInterleavingDistance_le_gromovProkhorovEDist
    (d : MetricSpace X) (e : MetricSpace Y) (R : Type w) [Ring R] (n : ℕ) :
    subdivisionRipsHomologyInterleavingDistance d e R n ≤
      @gromovProkhorovEDist X Y d e inferInstance inferInstance inferInstance inferInstance := by
  classical
  letI : MetricSpace X := d
  letI : MetricSpace Y := e
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  by_contra hnot
  have hGP : gromovProkhorovEDist X Y < (r : ℝ≥0∞) := lt_of_not_ge hnot
  obtain ⟨δ, hGPδ, hδr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hGP
  have hExists : subdivisionRipsHomologyInterleavingExistsAt δ d e R n := by
    let s : SupNormWitness X Y δ := supNormWitness δ hGPδ
    exact ⟨s.homologyInterleaving R n, s.homologyInterleaving_left R n,
      s.homologyInterleaving_right R n⟩
  have hdist : subdivisionRipsHomologyInterleavingDistance d e R n ≤
      (δ : ℝ≥0∞) := by
    unfold subdivisionRipsHomologyInterleavingDistance
    exact (iInf_le
      (fun ε : ℝ≥0 =>
        if subdivisionRipsHomologyInterleavingExistsAt ε d e R n then
          (ε : ℝ≥0∞) else ∞) δ).trans (by simp [hExists])
  exact (not_lt_of_ge hdist) (hδr.trans hr)
end
end TDA.Topology.FiniteGromovProkhorov
