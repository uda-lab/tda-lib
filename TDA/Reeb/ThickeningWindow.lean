import TDA.Reeb.ThickeningSlice

/-!
# Windows and transfers of a cylinder presentation

For a cylinder presentation `P` over levels `S`, a half-width `ε ≥ 0` and a height `c`, the window
of the realization `X = P.Realization S` at `c` and the transfers between windows (de Silva–Munch–
Patel, *Categorified Reeb Graphs*, proof of Theorem 4.27). The pieces of `P` are arbitrary
topological spaces; no separation hypothesis is used anywhere, and `ε = 0` is allowed.

## Windows

The raw window `P.WindowRaw S ε c` is the finite sum of the vertex pieces `V i` times their
degenerate slices `J_i(c) = slice (a i) (a i) ε c`, which are `{a i}` or empty, and the edge pieces
`E e` times their slices `J_e(c) = slice (a e) (a (e+1)) ε c`. These are the level-`c` pieces of the
thickenings of the vertex strips and the cylinders. `windowIncl` sends a raw window point to the
corresponding raw point of `P`; its height lies in `[c - ε, c + ε]`
(`rawHeight_windowIncl_mem`).

The window `P.Window S ε c` is the quotient of the raw window by "same point of `X`"
(`windowSetoid`), with the quotient topology. So `windowMk` is a quotient map by definition
(`isQuotientMap_windowMk`), also after product with a locally compact space
(`isQuotientMap_prodMap_windowMk`), and two raw window points are identified exactly when their
normal forms agree (`windowMk_eq_iff`). The window maps continuously and injectively into `X`
(`windowToSpace`, `windowToSpace_injective`), with height in `[c - ε, c + ε]`
(`height_windowToSpace_mem`). It is compact, resp. locally path-connected, when all pieces are
(`instCompactSpaceWindow`, `instLocallyPathConnectedSpaceWindow`), as a quotient of a finite sum of
products of pieces with compact real intervals, and empty when all pieces are
(`instIsEmptyWindow`). The window is not claimed to be the subspace `h⁻¹[c - ε, c + ε]` of `X`;
without a Hausdorff hypothesis the quotient topology is the one used.

## Transfers

`P.transferRaw S ε c : C(P.WindowRaw S ε c × ℝ, P.Raw S)` is the raw joint transfer: a vertex
point is kept, and an edge parameter `σ` goes to `RGraph.fragAff (a e) (a (e+1)) ε c u σ`, clamped
to the segment. It is jointly continuous in the raw point and the target height `u`. Under
`RGraph.TransferOK S ε c u`, `rawTransfer` moves raw window points from `c` to `u` by the affine
fragment maps, also on the degenerate vertex slices, and lands in the raw window at `u`; the clamp is
then inactive (`transferRaw_eq`). The raw transfer respects the window gluing
(`windowMk_rawTransfer_eq`): a slice end at a segment end stays at that end
(`SliceTransfer.fragAff_eq_left`, `SliceTransfer.fragAff_eq_right`), so a glued point stays glued.
The converse fails: an unglued point can move to a glued one, so at a slab end the transfer need not
be injective. It descends to the continuous `transfer : C(Window c, Window u)`
(`transfer_windowMk`), which fixes vertex points of `X` and moves edge points by `fragAff`
(`windowToSpace_transfer_inl`, `windowToSpace_transfer_inr`).

Along a locally compact set `U` of target heights, all satisfying the transfer hypotheses, the
transfers form one jointly continuous map `transferFamily : C(Window c × U, X)`
(`transferFamily_apply`, `height_transferFamily_mem`), descended along the product quotient
`windowMk × id_U`. It is the first coordinate of the slab cylinders of the thickening presentation.

With transfer hypotheses in both directions the transfers are mutually inverse
(`rawTransfer_rawTransfer`, `transfer_transfer`) and give a homeomorphism `transferHomeomorph`.
This needs neither `ε > 0` nor nondegenerate slices: it uses the degenerate-uniform
`SliceTransfer.fragAff_fragAff`.

See `docs/math/reeb-thickening-constructible.md`.
-/

open Set Topology
open scoped NNReal

universe u

namespace TDA.Reeb

noncomputable section

namespace CylinderPresentation

open Thickening
open RGraph (fragAff TransferOK)

attribute [local instance] RGraph.locallyPathConnectedSpace_Icc

variable {n : ℕ} (S : CriticalValues n) (P : CylinderPresentation.{u} n) (ε : ℝ≥0)

/-! ### Windows -/

section Window

variable (c : ℝ)

/-- The raw window at height `c`: vertex pieces times their degenerate slices (`{a i}` or empty) and
edge pieces times their slices. -/
abbrev WindowRaw : Type u :=
  (Σ i, P.V i × slice (S.value i) (S.value i) ε c) ⊕
    (Σ e, P.E e × slice (S.value e.castSucc) (S.value e.succ) ε c)

/-- Raw window points as raw points of the presentation: forget the vertex slice, and include the
edge slice in the segment. -/
def windowIncl : P.WindowRaw S ε c → P.Raw S :=
  Sum.map (fun p => ⟨p.1, p.2.1⟩) fun q =>
    ⟨q.1, q.2.1, ⟨q.2.2, slice_subset_Icc _ _ _ _ q.2.2.2⟩⟩

@[simp] theorem windowIncl_inl (i : Fin (n + 1)) (v : P.V i)
    (σ : slice (S.value i) (S.value i) ε c) :
    P.windowIncl S ε c (.inl ⟨i, v, σ⟩) = .inl ⟨i, v⟩ :=
  rfl

@[simp] theorem windowIncl_inr (e : Fin n) (y : P.E e)
    (σ : slice (S.value e.castSucc) (S.value e.succ) ε c) :
    P.windowIncl S ε c (.inr ⟨e, y, σ⟩) = .inr ⟨e, y, ⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩⟩ :=
  rfl

theorem continuous_windowIncl : Continuous (P.windowIncl S ε c) := by
  refine Continuous.sumMap (continuous_sigma fun i => ?_) (continuous_sigma fun e => ?_)
  · dsimp only
    exact continuous_sigmaMk.comp continuous_fst
  · dsimp only
    exact continuous_sigmaMk.comp
      (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _))

/-- Raw window points have height in `[c - ε, c + ε]`. -/
theorem rawHeight_windowIncl_mem (r : P.WindowRaw S ε c) :
    P.rawHeight S (P.windowIncl S ε c r) ∈ Icc (c - ε) (c + ε) := by
  rcases r with ⟨i, v, σ⟩ | ⟨e, y, σ⟩
  · have h1 := slice_subset_Icc _ _ _ _ σ.2
    have h2 := slice_subset_window _ _ _ _ σ.2
    change S.value i ∈ Icc (c - ε) (c + ε)
    rwa [← le_antisymm h1.2 h1.1]
  · exact slice_subset_window _ _ _ _ σ.2

/-- Two raw window points are related when they have the same image in the realization. -/
def windowSetoid : Setoid (P.WindowRaw S ε c) := Setoid.ker (P.quotMk S ∘ P.windowIncl S ε c)

/-- The window at height `c`: raw window points modulo "same point of the realization", with the
quotient topology. -/
def Window : Type u := Quotient (P.windowSetoid S ε c)

instance instTopologicalSpaceWindow : TopologicalSpace (P.Window S ε c) :=
  inferInstanceAs (TopologicalSpace (Quotient (P.windowSetoid S ε c)))

/-- The quotient map from the raw window. -/
def windowMk (r : P.WindowRaw S ε c) : P.Window S ε c := Quotient.mk _ r

theorem isQuotientMap_windowMk : IsQuotientMap (P.windowMk S ε c) := isQuotientMap_quotient_mk'

theorem windowMk_surjective : Function.Surjective (P.windowMk S ε c) := Quotient.mk_surjective

theorem continuous_windowMk : Continuous (P.windowMk S ε c) :=
  (P.isQuotientMap_windowMk S ε c).continuous

/-- `windowMk × id_I` is a quotient map for every locally compact `I` (Issue #706 (1)). -/
theorem isQuotientMap_prodMap_windowMk (I : Type*) [TopologicalSpace I] [LocallyCompactSpace I] :
    IsQuotientMap (Prod.map (P.windowMk S ε c) (_root_.id : I → I)) :=
  TDA.Topology.isQuotientMap_prodMap_id_left (P.isQuotientMap_windowMk S ε c)

/-- **Window gluing.** Two raw window points are identified exactly when their normal forms in the
presentation agree. -/
theorem windowMk_eq_iff {r r' : P.WindowRaw S ε c} :
    P.windowMk S ε c r = P.windowMk S ε c r' ↔
      P.nf S (P.windowIncl S ε c r) = P.nf S (P.windowIncl S ε c r') :=
  ⟨fun h => (P.quotMk_eq_iff S).1 (Quotient.exact h),
    fun h => Quotient.sound ((P.quotMk_eq_iff S).2 h)⟩

/-- The continuous injection of the window into the realization. -/
def windowToSpace : C(P.Window S ε c, P.Realization S) where
  toFun := Quotient.lift (P.quotMk S ∘ P.windowIncl S ε c) fun _ _ h => h
  continuous_toFun :=
    ((P.continuous_quotMk S).comp (P.continuous_windowIncl S ε c)).quotient_lift _

@[simp] theorem windowToSpace_windowMk (r : P.WindowRaw S ε c) :
    P.windowToSpace S ε c (P.windowMk S ε c r) = P.quotMk S (P.windowIncl S ε c r) :=
  rfl

theorem windowToSpace_injective : Function.Injective (P.windowToSpace S ε c) := by
  rintro ⟨r⟩ ⟨r'⟩ h
  exact Quotient.sound h

theorem height_windowToSpace_windowMk (r : P.WindowRaw S ε c) :
    P.height S (P.windowToSpace S ε c (P.windowMk S ε c r)) =
      P.rawHeight S (P.windowIncl S ε c r) :=
  rfl

/-- Window points have height in `[c - ε, c + ε]`. -/
theorem height_windowToSpace_mem (ξ : P.Window S ε c) :
    P.height S (P.windowToSpace S ε c ξ) ∈ Icc (c - ε) (c + ε) := by
  obtain ⟨r, rfl⟩ := P.windowMk_surjective S ε c ξ
  exact P.rawHeight_windowIncl_mem S ε c r

/-- The window is compact when all pieces are: a quotient of a finite sum of products of pieces
with compact real intervals. No separation hypothesis is used. -/
instance instCompactSpaceWindow [∀ i, CompactSpace (P.V i)] [∀ e, CompactSpace (P.E e)] :
    CompactSpace (P.Window S ε c) :=
  inferInstanceAs (CompactSpace (Quotient (P.windowSetoid S ε c)))

/-- The window is locally path-connected when all pieces are: a quotient of a finite sum of products
of pieces with real intervals. No separation hypothesis is used. -/
instance instLocallyPathConnectedSpaceWindow [∀ i, LocallyPathConnectedSpace (P.V i)]
    [∀ e, LocallyPathConnectedSpace (P.E e)] : LocallyPathConnectedSpace (P.Window S ε c) :=
  inferInstanceAs (LocallyPathConnectedSpace (Quotient (P.windowSetoid S ε c)))

/-- The window is empty when all pieces are. -/
instance instIsEmptyWindow [∀ i, IsEmpty (P.V i)] [∀ e, IsEmpty (P.E e)] :
    IsEmpty (P.Window S ε c) :=
  ⟨fun ξ => by
    obtain ⟨r, -⟩ := P.windowMk_surjective S ε c ξ
    rcases r with ⟨_, v, _⟩ | ⟨_, y, _⟩
    exacts [isEmptyElim v, isEmptyElim y]⟩

end Window

/-! ### Transfers -/

section Transfer

private theorem continuous_fragAff_param (a d e c u : ℝ) : Continuous (fragAff a d e c u) := by
  unfold fragAff
  fun_prop

/-- **Raw joint transfer** from height `c`, as a function of the target height `u`: a vertex point
is kept, and an edge parameter `σ` goes to `fragAff (a e) (a (e+1)) ε c u σ`, clamped to the
segment. The clamp is inactive under the transfer hypotheses (`transferRaw_eq`). -/
def transferRaw (c : ℝ) : C(P.WindowRaw S ε c × ℝ, P.Raw S) where
  toFun := Sum.elim (fun p => .inl ⟨p.1.1, p.1.2.1⟩)
      ((fun q : Σ e, (P.E e × slice (S.value e.castSucc) (S.value e.succ) ε c) × ℝ =>
        .inr ⟨q.1, q.2.1.1, projIcc _ _ (S.value_castSucc_lt_succ q.1).le
          (fragAff (S.value q.1.castSucc) (S.value q.1.succ) ε c q.2.2 q.2.1.2)⟩) ∘
        Homeomorph.sigmaProdDistrib) ∘ Homeomorph.sumProdDistrib
  continuous_toFun := by
    refine (Continuous.sumElim ?_ ?_).comp Homeomorph.sumProdDistrib.continuous
    · have hv : Continuous fun x : (Σ i, P.V i × slice (S.value i) (S.value i) ε c) =>
          (⟨x.1, x.2.1⟩ : P.VertexPiece) := continuous_sigma fun i => by
        dsimp only
        exact continuous_sigmaMk.comp continuous_fst
      exact continuous_inl.comp (hv.comp continuous_fst)
    · refine Continuous.comp ?_ Homeomorph.sigmaProdDistrib.continuous
      refine continuous_sigma fun e => ?_
      have hf : Continuous fun q : (P.E e × slice (S.value e.castSucc) (S.value e.succ) ε c) × ℝ =>
          projIcc _ _ (S.value_castSucc_lt_succ e).le
            (fragAff (S.value e.castSucc) (S.value e.succ) ε c q.2 q.1.2) :=
        continuous_projIcc.comp ((RGraph.continuous_fragAff _ _ _ c).comp
          ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
            continuous_snd))
      exact continuous_inr.comp (continuous_sigmaMk.comp
        ((continuous_fst.comp continuous_fst).prodMk hf))

@[simp] theorem transferRaw_inl (c u : ℝ) (i : Fin (n + 1)) (v : P.V i)
    (σ : slice (S.value i) (S.value i) ε c) :
    P.transferRaw S ε c (.inl ⟨i, v, σ⟩, u) = .inl ⟨i, v⟩ :=
  rfl

@[simp] theorem transferRaw_inr (c u : ℝ) (e : Fin n) (y : P.E e)
    (σ : slice (S.value e.castSucc) (S.value e.succ) ε c) :
    P.transferRaw S ε c (.inr ⟨e, y, σ⟩, u) =
      .inr ⟨e, y, projIcc _ _ (S.value_castSucc_lt_succ e).le
        (fragAff (S.value e.castSucc) (S.value e.succ) ε c u σ)⟩ :=
  rfl

/-- **Raw transfer** of window points from `c` to `u`: every slice parameter, on vertex and edge
pieces, moves by the affine fragment map of its segment. On a vertex slice it is fixed. -/
def rawTransfer {c u : ℝ} (h : TransferOK S ε c u) : P.WindowRaw S ε c → P.WindowRaw S ε u :=
  Sum.map (fun p => ⟨p.1, p.2.1, ⟨fragAff (S.value p.1) (S.value p.1) ε c u p.2.2,
      (h.sliceTransfer_vertex p.1).fragAff_mem p.2.2.2⟩⟩)
    fun q => ⟨q.1, q.2.1, ⟨fragAff (S.value q.1.castSucc) (S.value q.1.succ) ε c u q.2.2,
      (h.sliceTransfer_edge q.1).fragAff_mem q.2.2.2⟩⟩

@[simp] theorem rawTransfer_inl {c u : ℝ} (h : TransferOK S ε c u) (i : Fin (n + 1)) (v : P.V i)
    (σ : slice (S.value i) (S.value i) ε c) :
    P.rawTransfer S ε h (.inl ⟨i, v, σ⟩) =
      .inl ⟨i, v, ⟨fragAff (S.value i) (S.value i) ε c u σ,
        (h.sliceTransfer_vertex i).fragAff_mem σ.2⟩⟩ :=
  rfl

@[simp] theorem rawTransfer_inr {c u : ℝ} (h : TransferOK S ε c u) (e : Fin n) (y : P.E e)
    (σ : slice (S.value e.castSucc) (S.value e.succ) ε c) :
    P.rawTransfer S ε h (.inr ⟨e, y, σ⟩) =
      .inr ⟨e, y, ⟨fragAff (S.value e.castSucc) (S.value e.succ) ε c u σ,
        (h.sliceTransfer_edge e).fragAff_mem σ.2⟩⟩ :=
  rfl

theorem continuous_rawTransfer {c u : ℝ} (h : TransferOK S ε c u) :
    Continuous (P.rawTransfer S ε h) := by
  refine Continuous.sumMap (continuous_sigma fun i => ?_) (continuous_sigma fun e => ?_)
  · dsimp only
    exact continuous_sigmaMk.comp (continuous_fst.prodMk
      (((continuous_fragAff_param _ _ _ _ _).comp
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _))
  · dsimp only
    exact continuous_sigmaMk.comp (continuous_fst.prodMk
      (((continuous_fragAff_param _ _ _ _ _).comp
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _))

/-- Under the transfer hypotheses the raw joint transfer is the raw transfer into the window at
`u`: the clamp is inactive. -/
theorem transferRaw_eq {c u : ℝ} (h : TransferOK S ε c u) (r : P.WindowRaw S ε c) :
    P.transferRaw S ε c (r, u) = P.windowIncl S ε u (P.rawTransfer S ε h r) := by
  rcases r with ⟨i, v, σ⟩ | ⟨e, y, σ⟩
  · rfl
  · rw [transferRaw_inr, projIcc_of_mem _
      (slice_subset_Icc _ _ _ _ ((h.sliceTransfer_edge e).fragAff_mem σ.2))]
    rfl

/-- The transfer extended to the whole raw sum, clamped to each segment; normal forms are compared
through it in `nf_windowIncl_rawTransfer`. -/
private def transferNf (c u : ℝ) : P.Raw S → P.Raw S :=
  Sum.elim Sum.inl fun q => .inr ⟨q.1, q.2.1, projIcc _ _ (S.value_castSucc_lt_succ q.1).le
    (fragAff (S.value q.1.castSucc) (S.value q.1.succ) ε c u q.2.2)⟩

/-- The raw transfer commutes with normal forms, so it respects the window gluing. The outer `nf`
on the right is needed: an unglued slice end can move to a glued segment end. -/
private theorem nf_windowIncl_rawTransfer {c u : ℝ} (h : TransferOK S ε c u)
    (r : P.WindowRaw S ε c) :
    P.nf S (P.windowIncl S ε u (P.rawTransfer S ε h r)) =
      P.nf S (P.transferNf S ε c u (P.nf S (P.windowIncl S ε c r))) := by
  rcases r with ⟨i, v, σ⟩ | ⟨e, y, σ⟩
  · rfl
  · have hT := h.sliceTransfer_edge e
    have hmem := hT.fragAff_mem σ.2
    change P.nf S (.inr ⟨e, y, ⟨_, slice_subset_Icc _ _ _ _ hmem⟩⟩) =
      P.nf S (P.transferNf S ε c u (P.nf S (.inr ⟨e, y, ⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩⟩)))
    by_cases hsa : (σ : ℝ) = S.value e.castSucc
    · have h1 : (⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩ : Seg S e) = segBot S e := Subtype.ext hsa
      have h2 : (⟨_, slice_subset_Icc _ _ _ _ hmem⟩ : Seg S e) = segBot S e :=
        Subtype.ext (hT.fragAff_eq_left σ.2 hsa)
      rw [h1, h2, nf_segBot]
      rfl
    by_cases hsd : (σ : ℝ) = S.value e.succ
    · have h1 : (⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩ : Seg S e) = segTop S e := Subtype.ext hsd
      have h2 : (⟨_, slice_subset_Icc _ _ _ _ hmem⟩ : Seg S e) = segTop S e :=
        Subtype.ext (hT.fragAff_eq_right σ.2 hsd)
      rw [h1, h2, nf_segTop]
      rfl
    · have hnf : P.nf S (.inr ⟨e, y, ⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩⟩) =
          .inr ⟨e, y, ⟨σ, slice_subset_Icc _ _ _ _ σ.2⟩⟩ := by
        simp only [nf, nfCyl, Sum.elim_inr, hsa, hsd, ↓reduceIte]
      rw [hnf]
      simp only [transferNf, Sum.elim_inr]
      rw [projIcc_of_mem _ (slice_subset_Icc _ _ _ _ hmem)]

/-- **Descent.** The raw transfer respects the window gluing. -/
theorem windowMk_rawTransfer_eq {c u : ℝ} (h : TransferOK S ε c u) {r r' : P.WindowRaw S ε c}
    (hrr : P.windowMk S ε c r = P.windowMk S ε c r') :
    P.windowMk S ε u (P.rawTransfer S ε h r) = P.windowMk S ε u (P.rawTransfer S ε h r') := by
  rw [windowMk_eq_iff] at hrr ⊢
  rw [nf_windowIncl_rawTransfer, nf_windowIncl_rawTransfer, hrr]

/-- **Window transfer** `W(c) → W(u)`, descended from the raw affine maps. At a slab end it is
DMP's attaching map and need not be injective. -/
def transfer {c u : ℝ} (h : TransferOK S ε c u) : C(P.Window S ε c, P.Window S ε u) where
  toFun := Quotient.lift (P.windowMk S ε u ∘ P.rawTransfer S ε h) fun _ _ hrr =>
    P.windowMk_rawTransfer_eq S ε h (Quotient.sound hrr)
  continuous_toFun :=
    ((P.continuous_windowMk S ε u).comp (P.continuous_rawTransfer S ε h)).quotient_lift _

@[simp] theorem transfer_windowMk {c u : ℝ} (h : TransferOK S ε c u) (r : P.WindowRaw S ε c) :
    P.transfer S ε h (P.windowMk S ε c r) = P.windowMk S ε u (P.rawTransfer S ε h r) :=
  rfl

/-- In the realization, the transfer of a raw window point is the raw joint transfer. -/
theorem windowToSpace_transfer_windowMk {c u : ℝ} (h : TransferOK S ε c u)
    (r : P.WindowRaw S ε c) :
    P.windowToSpace S ε u (P.transfer S ε h (P.windowMk S ε c r)) =
      P.quotMk S (P.transferRaw S ε c (r, u)) := by
  rw [transferRaw_eq S P ε h]
  rfl

/-- The transfer fixes vertex points of the realization. -/
theorem windowToSpace_transfer_inl {c u : ℝ} (h : TransferOK S ε c u) (i : Fin (n + 1))
    (v : P.V i) (σ : slice (S.value i) (S.value i) ε c) :
    P.windowToSpace S ε u (P.transfer S ε h (P.windowMk S ε c (.inl ⟨i, v, σ⟩))) =
      P.ofVertex S i v :=
  rfl

/-- The transfer moves an edge point at parameter `σ` to parameter `fragAff … c u σ`. -/
theorem windowToSpace_transfer_inr {c u : ℝ} (h : TransferOK S ε c u) (e : Fin n) (y : P.E e)
    (σ : slice (S.value e.castSucc) (S.value e.succ) ε c) :
    P.windowToSpace S ε u (P.transfer S ε h (P.windowMk S ε c (.inr ⟨e, y, σ⟩))) =
      P.ofCylinder S e (y, ⟨fragAff (S.value e.castSucc) (S.value e.succ) ε c u σ,
        slice_subset_Icc _ _ _ _ ((h.sliceTransfer_edge e).fragAff_mem σ.2)⟩) :=
  rfl

/-- **Joint transfer** of the window at `c` to a locally compact set `U` of target heights, all
satisfying the transfer hypotheses: `(ξ, u) ↦ transfer ξ` in the realization. It is jointly
continuous, by descent along the product quotient `windowMk × id_U`. -/
def transferFamily (c : ℝ) {U : Set ℝ} [LocallyCompactSpace U] (hU : ∀ u : U, TransferOK S ε c u) :
    C(P.Window S ε c × U, P.Realization S) where
  toFun p := P.windowToSpace S ε p.2 (P.transfer S ε (hU p.2) p.1)
  continuous_toFun := by
    refine (P.isQuotientMap_prodMap_windowMk S ε c U).continuous_iff.2 ?_
    have hf : (fun p : P.Window S ε c × U => P.windowToSpace S ε p.2 (P.transfer S ε (hU p.2) p.1)) ∘
        Prod.map (P.windowMk S ε c) _root_.id =
          fun p => P.quotMk S (P.transferRaw S ε c (p.1, p.2)) := by
      funext p
      exact P.windowToSpace_transfer_windowMk S ε (hU p.2) p.1
    rw [hf]
    exact (P.continuous_quotMk S).comp ((P.transferRaw S ε c).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

@[simp] theorem transferFamily_apply (c : ℝ) {U : Set ℝ} [LocallyCompactSpace U]
    (hU : ∀ u : U, TransferOK S ε c u) (ξ : P.Window S ε c) (u : U) :
    P.transferFamily S ε c hU (ξ, u) = P.windowToSpace S ε u (P.transfer S ε (hU u) ξ) :=
  rfl

/-- The joint transfer to height `u` has height in `[u - ε, u + ε]`. -/
theorem height_transferFamily_mem (c : ℝ) {U : Set ℝ} [LocallyCompactSpace U]
    (hU : ∀ u : U, TransferOK S ε c u) (p : P.Window S ε c × U) :
    P.height S (P.transferFamily S ε c hU p) ∈ Icc ((p.2 : ℝ) - ε) (p.2 + ε) :=
  P.height_windowToSpace_mem S ε _ _

/-- **Degenerate-uniform interior inverse.** With transfer hypotheses in both directions, the raw
transfers `c → u` and `u → c` are mutually inverse. Neither `ε > 0` nor nondegenerate slices are
assumed. -/
theorem rawTransfer_rawTransfer {c u : ℝ} (h : TransferOK S ε c u) (h' : TransferOK S ε u c)
    (r : P.WindowRaw S ε c) : P.rawTransfer S ε h' (P.rawTransfer S ε h r) = r := by
  rcases r with ⟨i, v, σ⟩ | ⟨e, y, σ⟩
  · exact congrArg Sum.inl (Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Subtype.ext
      ((h.sliceTransfer_vertex i).fragAff_fragAff (h'.sliceTransfer_vertex i) σ.2)))))
  · exact congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Prod.ext rfl (Subtype.ext
      ((h.sliceTransfer_edge e).fragAff_fragAff (h'.sliceTransfer_edge e) σ.2)))))

/-- **Interior inverse.** With transfer hypotheses in both directions (for instance two heights of
one open slab of a grid listing the shifted levels), the transfers are mutually inverse. -/
theorem transfer_transfer {c u : ℝ} (h : TransferOK S ε c u) (h' : TransferOK S ε u c)
    (ξ : P.Window S ε c) : P.transfer S ε h' (P.transfer S ε h ξ) = ξ := by
  obtain ⟨r, rfl⟩ := P.windowMk_surjective S ε c ξ
  rw [transfer_windowMk, transfer_windowMk, rawTransfer_rawTransfer]

theorem transfer_injective {c u : ℝ} (h : TransferOK S ε c u) (h' : TransferOK S ε u c) :
    Function.Injective (P.transfer S ε h) :=
  Function.LeftInverse.injective (P.transfer_transfer S ε h h')

/-- With transfer hypotheses in both directions, the transfer is a homeomorphism
`W(c) ≃ₜ W(u)`, for every `ε ≥ 0`. -/
def transferHomeomorph {c u : ℝ} (h : TransferOK S ε c u) (h' : TransferOK S ε u c) :
    P.Window S ε c ≃ₜ P.Window S ε u where
  toFun := P.transfer S ε h
  invFun := P.transfer S ε h'
  left_inv := P.transfer_transfer S ε h h'
  right_inv := P.transfer_transfer S ε h' h
  continuous_toFun := (P.transfer S ε h).continuous
  continuous_invFun := (P.transfer S ε h').continuous

@[simp] theorem transferHomeomorph_apply {c u : ℝ} (h : TransferOK S ε c u)
    (h' : TransferOK S ε u c) (ξ : P.Window S ε c) :
    P.transferHomeomorph S ε h h' ξ = P.transfer S ε h ξ :=
  rfl

@[simp] theorem transferHomeomorph_symm_apply {c u : ℝ} (h : TransferOK S ε c u)
    (h' : TransferOK S ε u c) (ξ : P.Window S ε u) :
    (P.transferHomeomorph S ε h h').symm ξ = P.transfer S ε h' ξ :=
  rfl

end Transfer

end CylinderPresentation

end

end TDA.Reeb
