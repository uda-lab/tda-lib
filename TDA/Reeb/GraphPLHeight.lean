import TDA.Reeb.GraphRealization
import TDA.Reeb.Interval
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.ProjIcc

/-!
# Piecewise-linear heights on realizations of simple graphs

For `V : Type u`, `G : SimpleGraph V` and vertex heights `h : V → ℝ`, the affine height of a dart
`d` at `t : unitInterval` is `dartHeight h d t = (1 - t) * h d.fst + t * h d.snd`. It satisfies the
reversal equation `dartHeight h d.symm (σ t) = dartHeight h d t` and the start equation
`dartHeight h d 0 = h d.fst`, so the universal lift `TDA.Reeb.GraphRealization.continuousLift`
gives the piecewise-linear height `plHeight G h : C(Realization G, ℝ)`, with
`plHeight G h (vertex G v) = h v` and `plHeight G h (edgePoint G d t) = dartHeight h d t` by `rfl`
and uniqueness among continuous maps with these values (`plHeight_unique`). Equal endpoint heights
are allowed: a horizontal dart has constant height (`dartHeight_of_eq`).

## Unoriented edges and their support

An unoriented edge is an element of mathlib's edge set `G.edgeSet`. `dartEdge d` is the edge of
the dart `d`, and two darts have the same edge exactly when they are equal or opposite
(`dartEdge_eq_iff`). For an open interval `I`, `EdgeActive G h I e` holds when some dart of `e`
has an interior parameter `0 < t < 1` whose height lies in `I`. Activity:

* does not depend on the orientation (`edgeActive_dartEdge_iff`, `EdgeActive.exists_mem`);
* is monotone in `I` (`EdgeActive.mono`);
* is equivalent to nonemptiness of the full parameter set `{t : unitInterval // dartHeight h d t ∈ I}`
  (`edgeActive_dartEdge_iff_nonempty`), where the direction from an endpoint parameter uses the
  openness of `I` (`exists_interior_of_mem`);
* holds for every edge incident to a surviving endpoint (`edgeActive_of_mem`);
* holds for a horizontal edge exactly when its common height lies in `I`
  (`edgeActive_dartEdge_iff_of_eq`).

The real parameters whose affine height lies in an order-convex set form an order-convex set, also
for a horizontal dart (`ordConnected_preimage_lineHeight`). Hence two edge points of one dart in
the height preimage of `I` are joined by a path inside that preimage (`joinedIn_edgePoint`).

No finiteness, injectivity of heights, nonemptiness or decidability is assumed. The short name
`mono` of `EdgeActive.mono` also occurs as `TDA.Reeb.Interleaving.mono` and
`TDA.Filtration.FilterFunction.mono`.
-/

open SimpleGraph Topology Set CategoryTheory

/-- The reversal of the unit interval; `open unitInterval` would make `I` a token. -/
local notation "σ" => unitInterval.symm

universe u

namespace TDA.Reeb.GraphPL

open TDA.Reeb.GraphRealization

noncomputable section

section dartHeight

variable {V : Type u} {G : SimpleGraph V} (h : V → ℝ)

/-- The affine height `L_d(t) = (1 - t) h(d.fst) + t h(d.snd)` on the interval of a dart. -/
def dartHeight (d : G.Dart) (t : unitInterval) : ℝ :=
  (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd

theorem continuous_dartHeight (d : G.Dart) : Continuous (dartHeight h d) := by
  unfold dartHeight
  fun_prop

/-- Reversal: `L_(d.symm)(1 - t) = L_d(t)`. -/
theorem dartHeight_symm (d : G.Dart) (t : unitInterval) :
    dartHeight h d.symm (σ t) = dartHeight h d t := by
  show (1 - (σ t : ℝ)) * h d.snd + (σ t : ℝ) * h d.fst =
    (1 - (t : ℝ)) * h d.fst + (t : ℝ) * h d.snd
  rw [unitInterval.coe_symm_eq]
  ring

@[simp] theorem dartHeight_zero (d : G.Dart) : dartHeight h d 0 = h d.fst := by
  simp [dartHeight]

@[simp] theorem dartHeight_one (d : G.Dart) : dartHeight h d 1 = h d.snd := by
  simp [dartHeight]

/-- Equal endpoint heights: a horizontal dart has constant height. -/
theorem dartHeight_of_eq {d : G.Dart} (hd : h d.fst = h d.snd) (t : unitInterval) :
    dartHeight h d t = h d.fst := by
  rw [dartHeight, ← hd]
  ring

/-- The real parameters whose affine height lies in an order-convex set form an order-convex
set; the constant-height case is included. -/
theorem ordConnected_preimage_lineHeight (d : G.Dart) {s : Set ℝ} (hs : s.OrdConnected) :
    ((fun r : ℝ => (1 - r) * h d.fst + r * h d.snd) ⁻¹' s).OrdConnected := by
  rcases le_total (h d.fst) (h d.snd) with hab | hab
  · refine hs.preimage_mono fun r r' hrr' => ?_
    show (1 - r) * h d.fst + r * h d.snd ≤ (1 - r') * h d.fst + r' * h d.snd
    nlinarith [mul_nonneg (sub_nonneg.2 hrr') (sub_nonneg.2 hab)]
  · refine hs.preimage_anti fun r r' hrr' => ?_
    show (1 - r') * h d.fst + r' * h d.snd ≤ (1 - r) * h d.fst + r * h d.snd
    nlinarith [mul_nonneg (sub_nonneg.2 hrr') (sub_nonneg.2 hab)]

end dartHeight

section plHeight

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- The piecewise-linear height of the realization, from the universal lift `continuousLift`. -/
def plHeight : C(Realization G, ℝ) :=
  continuousLift G h (fun d => ⟨dartHeight h d, continuous_dartHeight h d⟩)
    (fun d t => dartHeight_symm h d t) (fun d => dartHeight_zero h d)

@[simp] theorem plHeight_vertex (v : V) : plHeight G h (vertex G v) = h v := rfl

@[simp] theorem plHeight_edgePoint (d : G.Dart) (t : unitInterval) :
    plHeight G h (edgePoint G d t) = dartHeight h d t := rfl

theorem plHeight_unique (g : C(Realization G, ℝ)) (hv : ∀ v, g (vertex G v) = h v)
    (he : ∀ d t, g (edgePoint G d t) = dartHeight h d t) : g = plHeight G h :=
  continuousLift_unique G _ _ _ _ g hv he

end plHeight

section edges

variable {V : Type u} {G : SimpleGraph V}

/-- The unoriented edge of a dart, as an element of mathlib's edge set. -/
def dartEdge (d : G.Dart) : G.edgeSet := ⟨d.edge, d.edge_mem⟩

@[simp] theorem coe_dartEdge (d : G.Dart) : (dartEdge d : Sym2 V) = d.edge := rfl

@[simp] theorem dartEdge_symm (d : G.Dart) : dartEdge d.symm = dartEdge d :=
  Subtype.ext d.edge_symm

theorem dartEdge_eq_iff {d₁ d₂ : G.Dart} :
    dartEdge d₁ = dartEdge d₂ ↔ d₁ = d₂ ∨ d₁ = d₂.symm :=
  Subtype.ext_iff.trans (dart_edge_eq_iff d₁ d₂)

theorem mem_dartEdge {d : G.Dart} {v : V} :
    v ∈ (dartEdge d : Sym2 V) ↔ v = d.fst ∨ v = d.snd :=
  Sym2.mem_iff

theorem fst_mem_dartEdge (d : G.Dart) : d.fst ∈ (dartEdge d : Sym2 V) := Sym2.mem_mk_left _ _

theorem snd_mem_dartEdge (d : G.Dart) : d.snd ∈ (dartEdge d : Sym2 V) := Sym2.mem_mk_right _ _

theorem exists_dartEdge_eq (e : G.edgeSet) : ∃ d : G.Dart, dartEdge d = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b => exact ⟨⟨(a, b), he⟩, rfl⟩

/-- Every endpoint of an edge is the start of a representing dart. -/
theorem exists_dartEdge_eq_fst {e : G.edgeSet} {v : V} (hv : v ∈ (e : Sym2 V)) :
    ∃ d : G.Dart, dartEdge d = e ∧ d.fst = v := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ⟨⟨(v, b), he⟩, rfl, rfl⟩
    · exact ⟨⟨(v, a), (G.mem_edgeSet.1 he).symm⟩, Subtype.ext Sym2.eq_swap, rfl⟩

end edges

section support

variable {V : Type u} (G : SimpleGraph V) (h : V → ℝ)

/-- An unoriented edge is active over `I` when some representing dart has an interior parameter
`0 < t < 1` whose affine height lies in `I`. -/
def EdgeActive (I : OpenInterval) (e : G.edgeSet) : Prop :=
  ∃ d : G.Dart, dartEdge d = e ∧
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ I

variable {G h} {I J : OpenInterval}

/-- Openness of `I`: a parameter in the height preimage, interior or not, yields an interior one. -/
theorem exists_interior_of_mem {d : G.Dart} {t : unitInterval} (ht : dartHeight h d t ∈ I) :
    ∃ s : unitInterval, 0 < (s : ℝ) ∧ (s : ℝ) < 1 ∧ dartHeight h d s ∈ I := by
  have hc : Continuous fun r : ℝ => (1 - r) * h d.fst + r * h d.snd := by fun_prop
  have hmem : (t : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact t.2
  obtain ⟨r, hrI, hr⟩ := mem_closure_iff_nhds.1 hmem _
    (hc.continuousAt.preimage_mem_nhds (I.isOpen.mem_nhds ht))
  exact ⟨⟨r, Ioo_subset_Icc_self hr⟩, hr.1, hr.2, hrI⟩

theorem EdgeActive.mono (hIJ : I ≤ J) {e : G.edgeSet} (he : EdgeActive G h I e) :
    EdgeActive G h J e := by
  obtain ⟨d, hd, t, ht₀, ht₁, ht⟩ := he
  exact ⟨d, hd, t, ht₀, ht₁, OpenInterval.le_iff_subset.1 hIJ ht⟩

/-- **Orientation independence.** An edge is active exactly when any one of its darts has an
interior parameter in the height preimage. -/
theorem edgeActive_dartEdge_iff (d : G.Dart) :
    EdgeActive G h I (dartEdge d) ↔
      ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ I := by
  constructor
  · rintro ⟨d', hd', t, ht₀, ht₁, ht⟩
    rcases dartEdge_eq_iff.1 hd' with rfl | rfl
    · exact ⟨t, ht₀, ht₁, ht⟩
    · refine ⟨σ t, ?_, ?_, ?_⟩
      · rw [unitInterval.coe_symm_eq]; linarith
      · rw [unitInterval.coe_symm_eq]; linarith
      · have hrev := dartHeight_symm h d.symm t
        rw [Dart.symm_symm] at hrev
        rwa [hrev]
  · rintro ⟨t, ht₀, ht₁, ht⟩
    exact ⟨d, rfl, t, ht₀, ht₁, ht⟩

/-- Activity is nonemptiness of the full restricted parameter set `E_d(I)`; the direction from an
arbitrary, possibly endpoint, parameter uses the openness of `I`. -/
theorem edgeActive_dartEdge_iff_nonempty (d : G.Dart) :
    EdgeActive G h I (dartEdge d) ↔ Nonempty {t : unitInterval // dartHeight h d t ∈ I} := by
  rw [edgeActive_dartEdge_iff]
  constructor
  · rintro ⟨t, -, -, ht⟩
    exact ⟨⟨t, ht⟩⟩
  · rintro ⟨t, ht⟩
    exact exists_interior_of_mem ht

theorem edgeActive_dartEdge_of_mem {d : G.Dart} {t : unitInterval} (ht : dartHeight h d t ∈ I) :
    EdgeActive G h I (dartEdge d) :=
  (edgeActive_dartEdge_iff_nonempty d).2 ⟨⟨t, ht⟩⟩

/-- Orientation independence for an arbitrary representing dart of an active edge. -/
theorem EdgeActive.exists_mem {e : G.edgeSet} (he : EdgeActive G h I e) {d : G.Dart}
    (hd : dartEdge d = e) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ dartHeight h d t ∈ I := by
  subst hd
  exact (edgeActive_dartEdge_iff d).1 he

/-- A surviving endpoint makes every incident edge active. -/
theorem edgeActive_of_mem {e : G.edgeSet} {v : V} (hv : v ∈ (e : Sym2 V)) (hI : h v ∈ I) :
    EdgeActive G h I e := by
  obtain ⟨d, rfl, rfl⟩ := exists_dartEdge_eq_fst hv
  exact edgeActive_dartEdge_of_mem (t := 0) (by rwa [dartHeight_zero])

/-- A horizontal edge is active exactly when its common height lies in `I`. -/
theorem edgeActive_dartEdge_iff_of_eq {d : G.Dart} (hd : h d.fst = h d.snd) :
    EdgeActive G h I (dartEdge d) ↔ h d.fst ∈ I := by
  rw [edgeActive_dartEdge_iff_nonempty]
  constructor
  · rintro ⟨t, ht⟩
    rwa [dartHeight_of_eq h hd] at ht
  · intro hI
    exact ⟨⟨0, by rwa [dartHeight_zero]⟩⟩

/-- **Convex edge fragments.** Two parameters of one dart in the height preimage are joined by a
path inside the preimage: the parameters of an order-convex interval under the affine height form
a convex set, also for a horizontal dart. -/
theorem joinedIn_edgePoint (d : G.Dart) {s t : unitInterval} (hs : dartHeight h d s ∈ I)
    (ht : dartHeight h d t ∈ I) :
    JoinedIn (plHeight G h ⁻¹' (I : Set ℝ)) (edgePoint G d s) (edgePoint G d t) := by
  have hF : Convex ℝ
      (Icc (0 : ℝ) 1 ∩ (fun r : ℝ => (1 - r) * h d.fst + r * h d.snd) ⁻¹' (I : Set ℝ)) :=
    (convex_Icc 0 1).inter
      (convex_iff_ordConnected.2 (ordConnected_preimage_lineHeight h d I.ordConnected))
  have hJ := (hF.isPathConnected ⟨s, s.2, hs⟩).joinedIn (s : ℝ) ⟨s.2, hs⟩ (t : ℝ) ⟨t.2, ht⟩
  have hc : Continuous fun r : ℝ => edgePoint G d (projIcc 0 1 zero_le_one r) :=
    (continuous_edgePoint G d).comp continuous_projIcc
  have hsub : (fun r : ℝ => edgePoint G d (projIcc 0 1 zero_le_one r)) ''
      (Icc (0 : ℝ) 1 ∩ (fun r : ℝ => (1 - r) * h d.fst + r * h d.snd) ⁻¹' (I : Set ℝ)) ⊆
        plHeight G h ⁻¹' (I : Set ℝ) := by
    rintro _ ⟨r, ⟨hr, hrI⟩, rfl⟩
    show dartHeight h d (projIcc 0 1 zero_le_one r) ∈ I
    rw [projIcc_of_mem _ hr]
    exact hrI
  simpa only [projIcc_val] using (hJ.map hc).mono hsub

end support

end

end TDA.Reeb.GraphPL
