import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import TDA.Sheaf.BandIntervalFibreCohomology
import TDA.Sheaf.BandIntervalMaps

/-!
# Degree-one convolution of real interval sheaves

For a bounded open interval, the long exact sequence identifies degree-one convolution with
the cokernel of degree-zero convolution of the restriction from the closed interval to the
pair of endpoint sheaves. On the overlap of the two convolved endpoint supports, the
cokernel is the interval sheaf of the closed overlap.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  DerivedCategory TopologicalSpace Opposite TDA.Persistence

namespace TDA.Sheaf.BandConvolution

open RealStratification RealConstructible AlternatingDiagram

variable {k : Type} [Field k] {m : ℕ} {p : Fin m → ℝ}

private theorem exists_eq_Ioo_of_mem_outSet1 {I : Set ℝ} (hI : I.OrdConnected)
    {ε y : ℝ} (hy : y ∈ outSet1 ε I) :
    ∃ a b, a < b ∧ I = Set.Ioo a b := by
  obtain ⟨hne, hO, hsub⟩ := hy
  have hl : BddBelow I := ⟨y - ε, fun _ hx => (hsub (subset_closure hx)).1⟩
  have hu : BddAbove I := ⟨y + ε, fun _ hx => (hsub (subset_closure hx)).2⟩
  have hcl : closure I = Set.Icc (sInf I) (sSup I) := by
    refine Set.Subset.antisymm (closure_minimal
      (fun x hx => ⟨csInf_le hl hx, le_csSup hu hx⟩) isClosed_Icc) ?_
    exact (convex_iff_ordConnected.1 (convex_iff_ordConnected.2 hI).closure).out
      (csInf_mem_closure hne hl) (csSup_mem_closure hne hu)
  have hoe : interior (closure I) = I := by
    rw [(convex_iff_ordConnected.2 hI).interior_closure_eq_interior_of_nonempty_interior
      (by rwa [hO.interior_eq]), hO.interior_eq]
  rw [hcl, interior_Icc] at hoe
  exact ⟨sInf I, sSup I, Set.nonempty_Ioo.mp (hoe.symm ▸ hne), hoe.symm⟩

/-- A nonempty degree-one output forces the degree-zero output of an interval to be empty. -/
theorem outSet0_eq_empty_of_outSet1_nonempty {ε : ℝ} (hε : 0 ≤ ε) {I : Set ℝ}
    (hI : I.OrdConnected) (h₁ : (outSet1 ε I).Nonempty) : outSet0 ε I = ∅ := by
  obtain ⟨y, hy⟩ := h₁
  obtain ⟨a, b, hab, rfl⟩ := exists_eq_Ioo_of_mem_outSet1 hI hy
  rw [outSet1_Ioo hε hab] at hy
  rw [outSet0_Ioo hε hab, Set.Ioo_eq_empty_of_le (show b - ε ≤ a + ε from hy.1.trans hy.2)]

private theorem mem_breakpoints_of_excluded_endpoint (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {a : ℝ}
    (ha : a ∈ closure (intervalSet p J) \ intervalSet p J) :
    a ∈ breakpoints p := by
  obtain ⟨v, hv⟩ := exists_mem_stratum hp a
  rcases Nat.even_or_odd' v.val with ⟨j, h | h⟩
  · have ho : IsOpen (stratum p v) := by
      rw [stratum_of_even (show v.val % 2 = 0 by omega)]
      exact (star p v).isOpen
    obtain ⟨x, hx, hxI⟩ := mem_closure_iff.1 ha.1 _ ho hv
    exact (ha.2 ((mem_intervalSet_iff_alive hv).2 ((mem_intervalSet_iff_alive hx).1 hxI))).elim
  · exact mem_breakpoints.mpr ⟨⟨j, by have := v.isLt; omega⟩, (hv.2 _ h).symm⟩

private theorem exists_open_endpoints (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {ε : ℝ} (hne : (outSet1 ε (intervalSet p J)).Nonempty) :
    ∃ i j : Fin m, i < j ∧ intervalSet p J = Set.Ioo (p i) (p j) := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨a, b, hab, hJ⟩ := exists_eq_Ioo_of_mem_outSet1 (ordConnected_intervalSet hp J) hy
  have ha : a ∈ breakpoints p := mem_breakpoints_of_excluded_endpoint hp J (by
    rw [hJ, closure_Ioo hab.ne]
    exact ⟨⟨le_rfl, hab.le⟩, fun h => lt_irrefl _ h.1⟩)
  have hb : b ∈ breakpoints p := mem_breakpoints_of_excluded_endpoint hp J (by
    rw [hJ, closure_Ioo hab.ne]
    exact ⟨⟨hab.le, le_rfl⟩, fun h => lt_irrefl _ h.2⟩)
  obtain ⟨i, rfl⟩ := mem_breakpoints.mp ha
  obtain ⟨j, rfl⟩ := mem_breakpoints.mp hb
  exact ⟨i, j, hp.lt_iff_lt.mp hab, hJ⟩

/-- A nonempty degree-one output is an interval on the shifted breakpoint stratification. -/
theorem exists_intervalSet_outSet1 (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hne : (outSet1 ε (intervalSet p J)).Nonempty) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet (sortedBreakpoints (bandBreakpoints p ε)) K = outSet1 ε (intervalSet p J) := by
  obtain ⟨i, j, hij, hJ⟩ := exists_open_endpoints hp J hne
  obtain ⟨y, hy⟩ := hne
  have ha := apply_mem_breakpoints p i
  have hb := apply_mem_breakpoints p j
  have hab := hp hij
  let q := sortedBreakpoints (bandBreakpoints p ε)
  have hq : StrictMono q := strictMono_sortedBreakpoints (bandBreakpoints p ε)
  obtain ⟨l, hl⟩ : ∃ l, q l = p j - ε := mem_breakpoints.mp (by
    rw [breakpoints_sortedBreakpoints]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem (· - ε) hb))
  obtain ⟨r, hr⟩ : ∃ r, q r = p i + ε := mem_breakpoints.mp (by
    rw [breakpoints_sortedBreakpoints]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem (· + ε) ha))
  rw [hJ, outSet1_Ioo hε hab] at hy ⊢
  have hlr : l ≤ r := hq.le_iff_le.mp (by rw [hl, hr]; exact hy.1.trans hy.2)
  let K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1) :=
    ⟨2 * l.val + 1, 2 * r.val + 2, by have := Fin.le_def.mp hlr; omega,
      by have := r.isLt; omega⟩
  exact ⟨K, by rw [intervalSet_eq_Icc hq (J := K) rfl rfl, hl, hr]⟩

section EndpointSequence

private def overlapMap (A B : FiniteInterval (2 * m + 1)) (v : Fin (2 * m + 1)) :
    A.fiber (k := k) v →ₗ[k] B.fiber (k := k) v :=
  if h : A.alive v ∧ B.alive v then
    Submodule.inclusion (by simp [FiniteInterval.fiber, h.1, h.2])
  else 0

private theorem overlapMap_val (A B : FiniteInterval (2 * m + 1))
    (v : Fin (2 * m + 1)) (x : A.fiber (k := k) v) :
    (overlapMap A B v x : k) = if A.alive v ∧ B.alive v then (x : k) else 0 := by
  by_cases h : A.alive v ∧ B.alive v <;> simp [overlapMap, h]

private def overlapHom (A B : FiniteInterval (2 * m + 1))
    (h : ∀ {v w}, Arrow (orient m) v w →
      (A.alive v ∧ A.alive w ∧ B.alive w ↔ A.alive v ∧ B.alive v ∧ B.alive w)) :
    interval (k := k) (orient m) A ⟶ interval (orient m) B :=
  homMk (fun v => ModuleCat.ofHom (overlapMap A B v)) (fun {v w} e => by
    simp only [interval, ofArrows_map_gen]
    ext x : 2
    apply Subtype.ext
    change A.fiber (k := k) v at x
    change (overlapMap A B w (fiberMap A v w x) : k) =
      (fiberMap B v w (overlapMap A B v x) : k)
    have he := h e
    by_cases hv : A.alive v <;> by_cases hw : A.alive w <;>
      by_cases hv' : B.alive v <;> by_cases hw' : B.alive w <;>
      simp_all [overlapMap_val, fiberMap_val])

private def endpoint (i : Fin m) : FiniteInterval (2 * m + 1) :=
  ⟨2 * i.val + 1, 2 * i.val + 2, by omega, by have := i.isLt; omega⟩

variable {i j : Fin m} (hij : i < j)

private def openSegment : FiniteInterval (2 * m + 1) :=
  ⟨2 * i.val + 2, 2 * j.val + 1, by have := Fin.lt_def.mp hij; omega,
    by have := j.isLt; omega⟩

private def closedSegment : FiniteInterval (2 * m + 1) :=
  ⟨2 * i.val + 1, 2 * j.val + 2, by have := Fin.lt_def.mp hij; omega,
    by have := j.isLt; omega⟩

private def openToClosed :
    interval (k := k) (orient m) (openSegment hij) ⟶ interval (orient m) (closedSegment hij) :=
  overlapHom _ _ (fun e => by
    have he := arrow_orient_iff.mp e
    have := Fin.lt_def.mp hij
    simp only [FiniteInterval.alive, openSegment, closedSegment]
    omega)

private def closedToLeft :
    interval (k := k) (orient m) (closedSegment hij) ⟶ interval (orient m) (endpoint i) :=
  overlapHom _ _ (fun e => by
    have he := arrow_orient_iff.mp e
    simp only [FiniteInterval.alive, closedSegment, endpoint]
    omega)

private def closedToRight :
    interval (k := k) (orient m) (closedSegment hij) ⟶ interval (orient m) (endpoint j) :=
  overlapHom _ _ (fun e => by
    have he := arrow_orient_iff.mp e
    simp only [FiniteInterval.alive, closedSegment, endpoint]
    omega)

private def endpointSequence : ShortComplex (Diagram k (orient m)) :=
  ShortComplex.mk (openToClosed hij)
    (biprod.lift (closedToLeft hij) (closedToRight hij)) (by
      apply biprod.hom_ext <;> apply NatTrans.ext <;> funext v
      all_goals
        let v : Fin (2 * m + 1) := v
      · rw [Category.assoc, biprod.lift_fst, zero_comp]
        ext x : 2
        apply Subtype.ext
        change (openSegment hij).fiber (k := k) v at x
        change (overlapMap (closedSegment hij) (endpoint i) v
          (overlapMap (openSegment hij) (closedSegment hij) v x) : k) = 0
        simp only [overlapMap_val]
        split_ifs <;> first
          | rfl
          | (simp only [FiniteInterval.alive, openSegment, closedSegment, endpoint] at *; omega)
      · rw [Category.assoc, biprod.lift_snd, zero_comp]
        ext x : 2
        apply Subtype.ext
        change (openSegment hij).fiber (k := k) v at x
        change (overlapMap (closedSegment hij) (endpoint j) v
          (overlapMap (openSegment hij) (closedSegment hij) v x) : k) = 0
        simp only [overlapMap_val]
        split_ifs <;> first
          | rfl
          | (simp only [FiniteInterval.alive, openSegment, closedSegment, endpoint] at *; omega))

private theorem endpointSequence_shortExact :
    (endpointSequence (k := k) hij).ShortExact := by
  let S := endpointSequence (k := k) hij
  let A := openSegment hij
  let B := closedSegment hij
  let L := endpoint i
  let R := endpoint j
  let P := interval (k := k) (orient m) L ⊞ interval (orient m) R
  let fst : P ⟶ interval (orient m) L := biprod.fst
  let snd : P ⟶ interval (orient m) R := biprod.snd
  have hends := Fin.lt_def.mp hij
  have hB (v : Fin (2 * m + 1)) : B.alive v ↔ A.alive v ∨ L.alive v ∨ R.alive v := by
    simp only [A, B, L, R, openSegment, closedSegment, endpoint, FiniteInterval.alive]
    omega
  have hLR (v : Fin (2 * m + 1)) : L.alive v → ¬ R.alive v := by
    simp only [L, R, endpoint, FiniteInterval.alive]
    omega
  have hf (v : Fin (2 * m + 1)) : Function.Injective (S.f.app (vtx (orient m) v)) := by
    intro x z h
    change A.fiber (k := k) v at x z
    change overlapMap A B v x = overlapMap A B v z at h
    apply Subtype.ext
    by_cases hv : A.alive v
    · have he : (overlapMap A B v x : k) = (overlapMap A B v z : k) :=
        congrArg Subtype.val h
      rw [overlapMap_val, overlapMap_val, ite_eq_left ⟨hv, (hB v).2 (Or.inl hv)⟩,
        ite_eq_left ⟨hv, (hB v).2 (Or.inl hv)⟩] at he
      exact he
    · rw [fiber_val_eq_zero hv x, fiber_val_eq_zero hv z]
  have hfst (v : Fin (2 * m + 1)) (x : B.fiber (k := k) v) :
      fst.app (vtx (orient m) v) (S.g.app (vtx (orient m) v) x) =
        overlapMap B L v x := by
    change ((biprod.lift (closedToLeft hij) (closedToRight hij) ≫ biprod.fst).app
      (vtx (orient m) v)) x = _
    rw [biprod.lift_fst]
    rfl
  have hsnd (v : Fin (2 * m + 1)) (x : B.fiber (k := k) v) :
      snd.app (vtx (orient m) v) (S.g.app (vtx (orient m) v) x) =
        overlapMap B R v x := by
    change ((biprod.lift (closedToLeft hij) (closedToRight hij) ≫ biprod.snd).app
      (vtx (orient m) v)) x = _
    rw [biprod.lift_snd]
    rfl
  have hg (v : Fin (2 * m + 1)) : Function.Surjective (S.g.app (vtx (orient m) v)) := by
    intro z
    let l : L.fiber (k := k) v := fst.app (vtx (orient m) v) z
    let r : R.fiber (k := k) v := snd.app (vtx (orient m) v) z
    have hlr : (l : k) ∈ B.fiber v := by
      by_cases h : L.alive v
      · simp [FiniteInterval.fiber, (hB v).2 (Or.inr (Or.inl h))]
      · rw [fiber_val_eq_zero h l]; exact Submodule.zero_mem _
    have hrr : (r : k) ∈ B.fiber v := by
      by_cases h : R.alive v
      · simp [FiniteInterval.fiber, (hB v).2 (Or.inr (Or.inr h))]
      · rw [fiber_val_eq_zero h r]; exact Submodule.zero_mem _
    let x : B.fiber (k := k) v := ⟨(l : k) + r, Submodule.add_mem _ hlr hrr⟩
    refine ⟨x, ?_⟩
    apply (biprodEquiv (interval (orient m) L) (interval (orient m) R) _).injective
    apply Prod.ext
    · change fst.app (vtx (orient m) v) (S.g.app (vtx (orient m) v) _) = l
      rw [hfst v x]
      apply Subtype.ext
      rw [overlapMap_val]
      by_cases h : L.alive v
      · simp [x, h, (hB v).2 (Or.inr (Or.inl h)), fiber_val_eq_zero (hLR v h) r]
      · simp [h, fiber_val_eq_zero h l]
    · change snd.app (vtx (orient m) v) (S.g.app (vtx (orient m) v) _) = r
      rw [hsnd v x]
      apply Subtype.ext
      rw [overlapMap_val]
      by_cases h : R.alive v
      · have hn : ¬ L.alive v := fun hl => hLR v hl h
        simp [x, h, (hB v).2 (Or.inr (Or.inr h)), fiber_val_eq_zero hn l]
      · simp [h, fiber_val_eq_zero h r]
  have (v : Paths (Vertex (orient m))) : Mono (S.f.app v) :=
    (ModuleCat.mono_iff_injective _).2 (hf v)
  have (v : Paths (Vertex (orient m))) : Epi (S.g.app v) :=
    (ModuleCat.epi_iff_surjective _).2 (hg v)
  change S.ShortExact
  refine ShortComplex.ShortExact.mk' ?_
    (NatTrans.mono_of_mono_app S.f) (NatTrans.epi_of_epi_app S.g)
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun v => IsZero.of_iso ?_
    (S.mapHomologyIso ((evaluation _ _).obj v)).symm
  rw [← ShortComplex.exact_iff_isZero_homology, ShortComplex.moduleCat_exact_iff]
  intro z hz
  change B.fiber (k := k) v at z
  change S.g.app v z = 0 at hz
  change ∃ x : A.fiber (k := k) v, overlapMap A B v x = z
  by_cases ha : A.alive v
  · let x : A.fiber (k := k) v := ⟨(z : k), by simp [FiniteInterval.fiber, ha]⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact (overlapMap_val A B v x).trans (ite_eq_left ⟨ha, (hB v).2 (Or.inl ha)⟩)
  refine ⟨0, (map_zero _).trans (Subtype.ext ?_)⟩
  change 0 = (z : k)
  by_cases hb : B.alive v
  · rcases (hB v).mp hb with h | hl | hr
    · exact (ha h).elim
    · have h := congrArg (fst.app (vtx (orient m) v)) hz
      have ht : overlapMap B L v z = 0 := (hfst v z).symm.trans (h.trans (map_zero _))
      have hval : (overlapMap B L v z : k) = 0 := congrArg Subtype.val ht
      exact ((overlapMap_val B L v z).symm.trans hval |> fun e =>
        (ite_eq_left ⟨hb, hl⟩).symm.trans e).symm
    · have h := congrArg (snd.app (vtx (orient m) v)) hz
      have ht : overlapMap B R v z = 0 := (hsnd v z).symm.trans (h.trans (map_zero _))
      have hval : (overlapMap B R v z : k) = 0 := congrArg Subtype.val ht
      exact ((overlapMap_val B R v z).symm.trans hval |> fun e =>
        (ite_eq_left ⟨hb, hr⟩).symm.trans e).symm
  · exact (fiber_val_eq_zero hb z).symm

end EndpointSequence

section Triangle

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

local notation "H[" k "," ε "," i "]" =>
  (Plus.singleFunctor _ 0 ⋙ T k ε ⋙ Plus.homologyFunctor _ i)

private def singleTrianglePlus {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) : Triangle (Plus C) :=
  Triangle.mk ((Plus.singleFunctor C 0).map S.f) ((Plus.singleFunctor C 0).map S.g)
    (Plus.ι.preimage (hS.singleδ ≫
      ((Plus.ι (C := C)).commShiftIso (1 : ℤ)).inv.app ((Plus.singleFunctor C 0).obj S.X₁)))

private theorem singleTrianglePlus_distinguished
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex C} (hS : S.ShortExact) : singleTrianglePlus hS ∈ distTriang _ := by
  change Plus.ι.mapTriangle.obj (singleTrianglePlus hS) ∈ distTriang _
  convert hS.singleTriangle_distinguished using 1
  let A := (Plus.singleFunctor C 0).obj S.X₁
  let e := (Plus.ι (C := C)).commShiftIso (1 : ℤ)
  let δ : (Plus.singleFunctor C 0).obj S.X₃ ⟶ A⟦(1 : ℤ)⟧ :=
    Plus.ι.preimage (hS.singleδ ≫ e.inv.app A)
  have hδ : Plus.ι.map δ ≫ e.hom.app A = hS.singleδ := by
    change Plus.ι.map (Plus.ι.preimage _) ≫ _ = _
    rw [Functor.map_preimage]
    let d : Plus.ι.obj ((Plus.singleFunctor C 0).obj S.X₃) ⟶
        (shiftFunctor _ (1 : ℤ)).obj (Plus.ι.obj A) := hS.singleδ
    exact (Category.assoc d (e.app A).inv (e.app A).hom).trans
      (congrArg (d ≫ ·) (e.app A).inv_hom_id |>.trans (Category.comp_id d))
  change Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g)
    (Plus.ι.map δ ≫ e.hom.app A) = _
  exact congrArg (fun d => Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) d) hδ

private theorem exists_H1T_isCokernel (ε : ℝ)
    {S : ShortComplex (realLine.Sheaf (ModuleCat k))} (hS : S.ShortExact)
    (hzero : IsZero ((H[k,ε,1]).obj S.X₂)) :
    ∃ δ : (H[k,ε,0]).obj S.X₃ ⟶ (H[k,ε,1]).obj S.X₁,
      ∃ h : (H[k,ε,0]).map S.g ≫ δ = 0, Nonempty (IsColimit (CokernelCofork.ofπ δ h)) := by
  let C := realLine.Sheaf (ModuleCat k)
  let triangle := singleTrianglePlus hS
  have htriangle := singleTrianglePlus_distinguished hS
  let Q := (T k ε).mapTriangle.obj triangle
  have hQ := (T k ε).map_distinguished _ htriangle
  let H := Plus.homologyFunctor C 0
  let seq := ShortComplex.mk _ _ (H.comp_homologySequenceδ Q hQ 0 1 (by norm_num))
  have he := H.homologySequence_exact₃ Q hQ 0 1 (by norm_num)
  have : Epi seq.g :=
    (H.homologySequence_exact₁ Q hQ 0 1 (by norm_num)).epi_f_iff.mpr (hzero.eq_of_tgt _ _)
  exact ⟨seq.g, seq.zero, ⟨he.gIsCokernel⟩⟩

private theorem isIso_H0T_map_app_of_mem (hp : StrictMono p)
    {A B : FiniteInterval (2 * m + 1)}
    (φ : (extension k hp).obj (interval _ A) ⟶ (extension k hp).obj (interval _ B))
    [Epi φ] (hA : IsClosed (intervalSet p A)) (hB : IsClosed (intervalSet p B))
    {ε : ℝ} {U : Opens realLine} (hU : (U : Set ℝ).OrdConnected)
    {x : ℝ} (hx : x ∈ bandOpen ε U) (hxA : x ∈ intervalSet p A) (hxB : x ∈ intervalSet p B) :
    IsIso (((H[k,ε,0]).map φ).hom.app (op U)) := by
  let F := (extension k hp).obj (interval _ A)
  let G := (extension k hp).obj (interval _ B)
  let W := bandOpen ε U
  have hF : IsIso (F.presheaf.germ W x hx) :=
    isIso_germ_extension_interval k hp A (ordConnected_bandOpen ε hU)
    (fun _ hz => hA.closure_eq ▸ hz.1) hx hxA
  have hG : IsIso (G.presheaf.germ W x hx) :=
    isIso_germ_extension_interval k hp B (ordConnected_bandOpen ε hU)
    (fun _ hz => hB.closure_eq ▸ hz.1) hx hxB
  let st := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) x
  obtain ⟨eF⟩ := nonempty_stalk_extension_interval_iso k hp hxA
  obtain ⟨eG⟩ := nonempty_stalk_extension_interval_iso k hp hxB
  have := eF.toLinearEquiv.symm.finiteDimensional
  have := eG.toLinearEquiv.symm.finiteDimensional
  have hr := eF.toLinearEquiv.finrank_eq.trans eG.toLinearEquiv.finrank_eq.symm
  have hst : IsIso (st.map φ) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have hsurj := (ModuleCat.epi_iff_surjective (st.map φ)).1 inferInstance
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).2 hsurj, hsurj⟩
  have he : IsIso (φ.hom.app (op W) ≫ G.presheaf.germ W x hx) := by
    rw [← TopCat.Presheaf.stalkFunctor_map_germ W x hx φ.hom]
    change IsIso (F.presheaf.germ W x hx ≫ st.map φ)
    exact IsIso.comp_isIso' hF hst
  have happ : IsIso (φ.hom.app (op (bandOpen ε U))) :=
    IsIso.of_isIso_comp_right (φ.hom.app (op W)) (G.presheaf.germ W x hx)
  have h := thickeningSectionsIso_hom_naturality k ε φ U hU
  have hcomp : IsIso (((H[k,ε,0]).map φ).hom.app (op U) ≫
      (H0TSectionsIso k ε G U hU).hom) := by
    change IsIso (((H[k,ε,0]).map φ).hom.app (op U) ≫
      ((H0TIso k ε).hom.app G).hom.app (op U) ≫
        (thickeningSectionsIso k ε G U hU).hom)
    rw [← Category.assoc]
    change IsIso (((H[k,ε,0]).map φ ≫ (H0TIso k ε).hom.app G).hom.app (op U) ≫ _)
    rw [(H0TIso k ε).hom.naturality φ]
    change IsIso ((((H0TIso k ε).hom.app F).hom.app (op U) ≫ _) ≫ _)
    rw [Category.assoc, h]
    change IsIso ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map
      ((H0TIso k ε).hom.app F) ≫
        (thickeningSectionsIso k ε F U hU).hom ≫ φ.hom.app (op (bandOpen ε U)))
    let ev := sheafToPresheaf (Opens.grothendieckTopology realLine) (ModuleCat k) ⋙
      (evaluation _ _).obj (op U)
    exact IsIso.comp_isIso' ((ev.mapIso ((H0TIso k ε).app F)).isIso_hom)
      (IsIso.comp_isIso' (thickeningSectionsIso k ε F U hU).isIso_hom happ)
  exact IsIso.of_isIso_comp_right _ (H0TSectionsIso k ε G U hU).hom

private theorem isIso_germ_top_H0T_of_closed (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {ε y : ℝ} (hε : 0 ≤ ε)
    (hc : IsClosed (outSet0 ε (intervalSet p J))) (hy : y ∈ outSet0 ε (intervalSet p J)) :
    IsIso (((H[k,ε,0]).obj ((extension k hp).obj (interval _ J))).presheaf.germ
      ⊤ y trivial) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_H0T (k := k) hp J hε ⟨y, hy⟩
  let q := sortedBreakpoints (bandBreakpoints p ε)
  let hq : StrictMono q := strictMono_sortedBreakpoints _
  let G := (extension k hq).obj (interval _ K)
  let U : Opens realLine := ⊤
  have hclosed : IsClosed (intervalSet q K) := hK.symm ▸ hc
  have hg : IsIso (G.presheaf.germ U y trivial) :=
    isIso_germ_extension_interval k hq K (U := U) Set.ordConnected_univ
      (fun _ hx => hclosed.closure_eq ▸ hx.1) trivial (hK.symm ▸ hy)
  let ev := sheafToPresheaf (Opens.grothendieckTopology realLine) (ModuleCat k) ⋙
    (evaluation _ _).obj (op U)
  let st := TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) y
  have he : IsIso (e.hom.hom.app (op U)) := (ev.mapIso e).isIso_hom
  have hs : IsIso (st.map e.hom.hom) := (st.mapIso ((sheafToPresheaf _ _).mapIso e)).isIso_hom
  let f := ((H[k,ε,0]).obj ((extension k hp).obj (interval _ J))).presheaf.germ U y trivial
  have hcomp : IsIso (f ≫ st.map e.hom.hom) :=
    (TopCat.Presheaf.stalkFunctor_map_germ U y trivial e.hom.hom).symm ▸
      IsIso.comp_isIso' he hg
  exact @IsIso.of_isIso_comp_right (ModuleCat k) _ _ _ _ f (st.map e.hom.hom) hs hcomp

variable [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))]

/-- At a centre in the degree-one output set, the stalk of degree-one convolution has
coefficient module `k`. It is the cokernel of the degree-zero endpoint restriction on stalks. -/
theorem nonempty_iso_stalk_H1T_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {ε y : ℝ} (hε : 0 ≤ ε) (hy : y ∈ outSet1 ε (intervalSet p J)) :
    Nonempty (((H[k,ε,1]).obj ((extension k hp).obj (interval _ J))).presheaf.stalk y ≅
      ModuleCat.of k k) := by
  obtain ⟨i, j, hij, hJ⟩ := exists_open_endpoints hp J ⟨y, hy⟩
  have hJ' : J = openSegment hij := by
    apply eq_of_alive_iff
    intro v
    obtain ⟨x, hx⟩ := stratum_nonempty hp v
    rw [← mem_intervalSet_iff_alive hx, ← mem_intervalSet_iff_alive hx, hJ,
      intervalSet_eq_Ioo hp (J := openSegment hij) rfl rfl]
  subst J
  have hwin : y ∈ Set.Icc (p j - ε) (p i + ε) := by
    simpa only [hJ, outSet1_Ioo hε (hp hij)] using hy
  let A := closedSegment hij
  let L := endpoint i
  let R := endpoint j
  let S := endpointSequence (k := k) hij
  let E := extension k hp
  let H₀ := H[k,ε,0]
  let st := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
    TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) y
  have ha : intervalSet p A = Set.Icc (p i) (p j) := intervalSet_eq_Icc hp rfl rfl
  have hl : intervalSet p L = {p i} := intervalSet_eq_singleton hp rfl rfl
  have hr : intervalSet p R = {p j} := intervalSet_eq_singleton hp rfl rfl
  have hSES : (S.map E).ShortExact := (endpointSequence_shortExact (k := k) hij).map_of_exact E
  obtain ⟨δ, hδ, ⟨hC⟩⟩ := exists_H1T_isCokernel ε hSES (by
    apply isZero_H1T_interval hp A hε
    rw [ha, outSet1_Icc hε (hp hij).le])
  have houtA : outSet0 ε (intervalSet p A) = Set.Icc (p i - ε) (p j + ε) := by
    rw [ha, outSet0_Icc hε (hp hij).le]
  have houtL : outSet0 ε (intervalSet p L) = Set.Icc (p i - ε) (p i + ε) := by
    rw [hl, outSet0_singleton hε]
  have houtR : outSet0 ε (intervalSet p R) = Set.Icc (p j - ε) (p j + ε) := by
    rw [hr, outSet0_singleton hε]
  have hyA : y ∈ outSet0 ε (intervalSet p A) := by
    rw [houtA]; exact ⟨by linarith [hwin.1, hp hij], by linarith [hwin.2, hp hij]⟩
  have hyL : y ∈ outSet0 ε (intervalSet p L) := by
    rw [houtL]; exact ⟨by linarith [hwin.1, hp hij], hwin.2⟩
  have hyR : y ∈ outSet0 ε (intervalSet p R) := by
    rw [houtR]; exact ⟨hwin.1, by linarith [hwin.2, hp hij]⟩
  let gL := E.map (closedToLeft (k := k) hij)
  let U : Opens realLine := ⊤
  have hU : (U : Set ℝ).OrdConnected := Set.ordConnected_univ
  have hmem : p i ∈ bandOpen ε U := le_bandOpen hε U trivial
  let π : S.X₃ ⟶ interval (orient m) L := biprod.fst
  have hπ : S.g ≫ π = closedToLeft (k := k) hij := biprod.lift_fst _ _
  have hπ' : (S.map E).g ≫ E.map π = gL :=
    (E.map_comp S.g π).symm.trans (congrArg E.map hπ)
  have hE : Epi (S.map E).g := hSES.epi_g
  have hP : Epi π := (inferInstance : Epi
    (biprod.fst : interval (orient m) L ⊞ interval (orient m) R ⟶ interval (orient m) L))
  have hP' : Epi (E.map π) := E.map_epi π
  have hgL : Epi gL := hπ' ▸ (inferInstance : Epi ((S.map E).g ≫ E.map π))
  have hL := isIso_H0T_map_app_of_mem hp gL (ha.symm ▸ isClosed_Icc)
    (hl.symm ▸ isClosed_singleton) hU hmem (ha.symm ▸ Set.left_mem_Icc.2 (hp hij).le)
    (hl.symm ▸ Set.mem_singleton _)
  have hgA := isIso_germ_top_H0T_of_closed (k := k) hp A hε (houtA.symm ▸ isClosed_Icc) hyA
  have hg₁ := isIso_germ_top_H0T_of_closed (k := k) hp L hε (houtL.symm ▸ isClosed_Icc) hyL
  have hcomp : IsIso ((H₀.obj (E.obj (interval _ A))).presheaf.germ U y trivial ≫
      st.map (H₀.map gL)) :=
    (TopCat.Presheaf.stalkFunctor_map_germ U y trivial (H₀.map gL).hom).symm ▸
      IsIso.comp_isIso' hL hg₁
  have hst : IsIso (st.map (H₀.map gL)) := IsIso.of_isIso_comp_left
    ((H₀.obj (E.obj (interval _ A))).presheaf.germ U y trivial) _
  let f := st.map (H₀.map (S.map E).g)
  have hf : Mono f := by
    let g := st.map (H₀.map (E.map π))
    have he : f ≫ g = st.map (H₀.map gL) :=
      (st.map_comp _ _).symm.trans (congrArg st.map
        ((H₀.map_comp _ _).symm.trans (congrArg H₀.map hπ')))
    have : IsIso (f ≫ g) := he.symm ▸ hst
    exact mono_of_mono _ g
  -- The source and target at the stalk have dimensions one and two.
  have hAD {I : FiniteInterval (2 * m + 1)} (hyI : y ∈ outSet0 ε (intervalSet p I)) :
      Nonempty (st.obj (H₀.obj (E.obj (interval _ I))) ≅ ModuleCat.of k k) := by
    obtain ⟨K, hK, ⟨e⟩⟩ := exists_intervalSheaf_H0T (k := k) hp I hε ⟨y, hyI⟩
    obtain ⟨eK⟩ := nonempty_stalk_extension_interval_iso k (strictMono_sortedBreakpoints _)
      (J := K) (hK.symm ▸ hyI)
    exact ⟨st.mapIso e ≪≫ eK⟩
  obtain ⟨eA⟩ := hAD hyA
  obtain ⟨eL⟩ := hAD hyL
  obtain ⟨eR⟩ := hAD hyR
  have := preservesBinaryBiproducts_of_preservesBiproducts E
  have := preservesBinaryBiproducts_of_preservesBiproducts H₀
  have := preservesBinaryBiproducts_of_preservesBiproducts st
  let eB : st.obj (H₀.obj (S.map E).X₃) ≅ ModuleCat.of k (k × k) :=
    st.mapIso (H₀.mapIso (E.mapBiprod _ _) ≪≫ H₀.mapBiprod _ _) ≪≫
      st.mapBiprod _ _ ≪≫ biprod.mapIso eL eR ≪≫ ModuleCat.biprodIsoProd _ _
  have hdimA : Module.finrank k (st.obj (H₀.obj (S.map E).X₂)) = 1 := by
    change Module.finrank k (st.obj (H₀.obj (E.obj (interval _ A)))) = 1
    simpa using eA.toLinearEquiv.finrank_eq
  have hdimB : Module.finrank k (st.obj (H₀.obj (S.map E).X₃)) = 2 := by
    simpa [Module.finrank_prod] using eB.toLinearEquiv.finrank_eq
  have : FiniteDimensional k (st.obj (H₀.obj (S.map E).X₃)) :=
    eB.toLinearEquiv.symm.finiteDimensional
  have hrank := (LinearEquiv.ofInjective f.hom ((ModuleCat.mono_iff_injective f).1 hf)).finrank_eq
  have hd := (LinearMap.range f.hom).finrank_quotient_add_finrank
  have hq : Module.finrank k (↑(st.obj (H₀.obj (S.map E).X₃)) ⧸ f.hom.range) = 1 := by
    change Module.finrank k (st.obj (H₀.obj (S.map E).X₂)) = _ at hrank
    change _ + _ = Module.finrank k (st.obj (H₀.obj (S.map E).X₃)) at hd
    omega
  let ec := ((CokernelCofork.ofπ δ hδ).mapIsColimit hC st).coconePointUniqueUpToIso
    (cokernelIsCokernel f)
  let eq := ModuleCat.cokernelIsoRangeQuotient f
  let eQ : (↑(st.obj (H₀.obj (S.map E).X₃)) ⧸ f.hom.range) ≃ₗ[k] k :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hq)
  exact ⟨ec ≪≫ eq ≪≫ eQ.toModuleIso⟩

omit [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem isConstructible_biprod {n : ℕ} {q : Fin n → ℝ} (hq : StrictMono q)
    {A B : realLine.Sheaf (ModuleCat k)} (hA : IsConstructible (breakpoints q) A)
    (hB : IsConstructible (breakpoints q) B) : IsConstructible (breakpoints q) (A ⊞ B) := by
  let E := extension k hq
  let a := (sections k q).obj A
  let b := (sections k q).obj B
  let eA : A ≅ E.obj a := (sectionsExtensionIso k hq).app ⟨A, hA⟩
  let eB : B ≅ E.obj b := (sectionsExtensionIso k hq).app ⟨B, hB⟩
  have := preservesBinaryBiproducts_of_preservesBiproducts E
  refine isConstructible_of_iso ((E.mapBiprod a b).trans (biprod.mapIso eA.symm eB.symm))
    (isConstructible_extension k hq fun v => ?_)
  let ev := (evaluation _ (ModuleCat k)).obj v
  have := preservesBinaryBiproducts_of_preservesBiproducts ev
  have : FiniteDimensional k (ev.obj a) := finiteDimensional_sections k hq hA v
  have : FiniteDimensional k (ev.obj b) := finiteDimensional_sections k hq hB v
  have : FiniteDimensional k ((ev.obj a) × (ev.obj b)) := inferInstance
  exact ((ev.mapBiprod a b) ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv.symm.finiteDimensional

omit [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem isConstructible_cokernel {n : ℕ} {q : Fin n → ℝ} (hq : StrictMono q)
    {A B : realLine.Sheaf (ModuleCat k)} (f : A ⟶ B)
    (hA : IsConstructible (breakpoints q) A) (hB : IsConstructible (breakpoints q) B) :
    IsConstructible (breakpoints q) (cokernel f) := by
  let E := extension k hq
  let Γ := sections k q
  let eA : A ≅ E.obj (Γ.obj A) := (sectionsExtensionIso k hq).app ⟨A, hA⟩
  let eB : B ≅ E.obj (Γ.obj B) := (sectionsExtensionIso k hq).app ⟨B, hB⟩
  let g := Γ.map f
  have hn : f ≫ eB.hom = eA.hom ≫ E.map g :=
    (sectionsExtensionIso k hq).hom.naturality
      (show (⟨A, hA⟩ : Constructible k q) ⟶ ⟨B, hB⟩ from ObjectProperty.homMk f)
  refine isConstructible_of_iso
    ((PreservesCokernel.iso E g).trans (cokernel.mapIso f (E.map g) eA eB hn).symm)
    (isConstructible_extension k hq fun v => ?_)
  let ev := (evaluation _ (ModuleCat k)).obj v
  have : FiniteDimensional k (ev.obj (Γ.obj B)) := finiteDimensional_sections k hq hB v
  exact ((PreservesCokernel.iso ev g) ≪≫
    ModuleCat.cokernelIsoRangeQuotient (ev.map g)).toLinearEquiv.symm.finiteDimensional

omit [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem isIso_section_restriction_biprod {A B : realLine.Sheaf (ModuleCat k)}
    {V U : Opens realLine} (h : V ≤ U)
    [IsIso (A.presheaf.map (homOfLE h).op)] [IsIso (B.presheaf.map (homOfLE h).op)] :
    IsIso ((A ⊞ B : realLine.Sheaf (ModuleCat k)).presheaf.map (homOfLE h).op) := by
  let ev (W : Opens realLine) : realLine.Sheaf (ModuleCat k) ⥤ ModuleCat k :=
    sheafToPresheaf (Opens.grothendieckTopology realLine) (ModuleCat k) ⋙
      (evaluation _ _).obj (op W)
  let e (W : Opens realLine) : (ev W).obj (A ⊞ B) ≅ (ev W).obj A ⊞ (ev W).obj B := by
    have : (ev W).Additive := ⟨fun {_ _} _ _ => rfl⟩
    letI := preservesBinaryBiproducts_of_preservesBiproducts (ev W)
    exact (ev W).mapBiprod A B
  have he : (A ⊞ B : realLine.Sheaf (ModuleCat k)).presheaf.map (homOfLE h).op ≫ (e V).hom =
      (e U).hom ≫ biprod.map (A.presheaf.map (homOfLE h).op) (B.presheaf.map (homOfLE h).op) := by
    apply biprod.hom_ext
    · simp only [e, Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst]
      erw [biprod.map_fst, biprod.lift_fst_assoc]
      let π : A ⊞ B ⟶ A := biprod.fst
      change (A ⊞ B : realLine.Sheaf (ModuleCat k)).presheaf.map (homOfLE h).op ≫
        π.hom.app (op V) = π.hom.app (op U) ≫ A.presheaf.map (homOfLE h).op
      exact π.hom.naturality (homOfLE h).op
    · simp only [e, Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd]
      erw [biprod.map_snd, biprod.lift_snd_assoc]
      let π : A ⊞ B ⟶ B := biprod.snd
      change (A ⊞ B : realLine.Sheaf (ModuleCat k)).presheaf.map (homOfLE h).op ≫
        π.hom.app (op V) = π.hom.app (op U) ≫ B.presheaf.map (homOfLE h).op
      exact π.hom.naturality (homOfLE h).op
  have hi : IsIso ((A ⊞ B : realLine.Sheaf (ModuleCat k)).presheaf.map
      (homOfLE h).op ≫ (e V).hom) := by
    rw [he]
    exact IsIso.comp_isIso' (e U).isIso_hom ((biprod.mapIso
      (asIso (A.presheaf.map (homOfLE h).op)) (asIso (B.presheaf.map (homOfLE h).op))).isIso_hom)
  exact IsIso.of_isIso_comp_right _ (e V).hom

omit [HasDerivedCategory (pt.Sheaf (ModuleCat k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat k))] in
private theorem isIso_H0T_restriction_of_mem (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : IsClosed (intervalSet p J)) {V U : Opens realLine}
    (h : V ≤ U) (hV : (V : Set ℝ).OrdConnected) (hU : (U : Set ℝ).OrdConnected)
    {x : ℝ} (hx : x ∈ (V : Set ℝ) ∩ outSet0 ε (intervalSet p J)) :
    IsIso (((H[k,ε,0]).obj ((extension k hp).obj (interval _ J))).presheaf.map
      (homOfLE h).op) := by
  let F := (extension k hp).obj (interval _ J)
  obtain ⟨z, hzI, hz⟩ := hx.2.1
  have hzV : z ∈ bandOpen ε V := by
    refine ⟨x, hx.1, ?_⟩
    rw [Real.dist_eq, abs_le]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hclosed {W : Opens realLine} : closure (intervalSet p J) ∩ W ⊆ intervalSet p J :=
    fun _ hz => hc.closure_eq ▸ hz.1
  have := isIso_map_extension_interval k hp J (bandOpen_mono_right ε h)
    (ordConnected_bandOpen ε hV) (ordConnected_bandOpen ε hU) hclosed hclosed hzV hzI
  have hi : IsIso (((H[k,ε,0]).obj F).presheaf.map (homOfLE h).op ≫
      (H0TSectionsIso k ε F V hV).hom) := by
    rw [H0TSectionsIso_hom_map hε F h hV hU]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (H0TSectionsIso k ε F V hV).hom

private theorem nonempty_iso_H1T_interval_shifted (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (hne : (outSet1 ε (intervalSet p J)).Nonempty)
    (K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1))
    (hK : intervalSet (sortedBreakpoints (bandBreakpoints p ε)) K =
      outSet1 ε (intervalSet p J)) :
    Nonempty ((H[k,ε,1]).obj ((extension k hp).obj (interval _ J)) ≅
      (extension k (strictMono_sortedBreakpoints _)).obj (interval _ K)) := by
  obtain ⟨i, j, hij, hJ⟩ := exists_open_endpoints hp J hne
  have hJ' : J = openSegment hij := by
    apply eq_of_alive_iff
    intro v
    obtain ⟨x, hx⟩ := stratum_nonempty hp v
    rw [← mem_intervalSet_iff_alive hx, ← mem_intervalSet_iff_alive hx, hJ,
      intervalSet_eq_Ioo hp (J := openSegment hij) rfl rfl]
  subst J
  let q := sortedBreakpoints (bandBreakpoints p ε)
  let hq : StrictMono q := strictMono_sortedBreakpoints _
  let E := extension k hp
  let H₀ := H[k,ε,0]
  let H₁ := H[k,ε,1]
  let S := endpointSequence (k := k) hij
  let F := H₁.obj (S.map E).X₁
  let B := H₀.obj (S.map E).X₃
  let L := H₀.obj (E.obj (interval _ (endpoint i)))
  let R := H₀.obj (E.obj (interval _ (endpoint j)))
  have ha : intervalSet p (closedSegment hij) = Set.Icc (p i) (p j) :=
    intervalSet_eq_Icc hp rfl rfl
  have hl : intervalSet p (endpoint i) = {p i} := intervalSet_eq_singleton hp rfl rfl
  have hr : intervalSet p (endpoint j) = {p j} := intervalSet_eq_singleton hp rfl rfl
  have hclosed : IsClosed (intervalSet q K) := by
    rw [hK, hJ, outSet1_Ioo hε (hp hij)]
    exact isClosed_Icc
  have hSES : (S.map E).ShortExact := (endpointSequence_shortExact (k := k) hij).map_of_exact E
  obtain ⟨δ, hδ, ⟨hc⟩⟩ := exists_H1T_isCokernel ε hSES (by
    apply isZero_H1T_interval hp (closedSegment hij) hε
    rw [ha, outSet1_Icc hε (hp hij).le])
  have := preservesBinaryBiproducts_of_preservesBiproducts E
  have := preservesBinaryBiproducts_of_preservesBiproducts H₀
  let e : B ≅ L ⊞ R := H₀.mapIso (E.mapBiprod _ _) ≪≫ H₀.mapBiprod _ _
  have con (I : FiniteInterval (2 * m + 1)) :
      IsConstructible (breakpoints q) (H₀.obj (E.obj (interval _ I))) := by
    rw [breakpoints_sortedBreakpoints]
    exact isConstructible_H0T_interval hp I hε
  have hB : IsConstructible (breakpoints q) B :=
    isConstructible_of_iso e.symm (isConstructible_biprod hq (con _) (con _))
  have hF : IsConstructible (breakpoints q) F :=
    isConstructible_of_iso ((cokernelIsCokernel _).coconePointUniqueUpToIso hc)
      (isConstructible_cokernel hq _ (con _) hB)
  have hG := isConstructible_extension k hq (M := interval _ K) (fun _ => inferInstance)
  have hrel {U : Opens realLine} : closure (intervalSet q K) ∩ U ⊆ intervalSet q K :=
    fun _ hx => hclosed.closure_eq ▸ hx.1
  -- The representing germ reads the quotient on each basic open.
  have sectionsAt {U : Opens realLine} (hU : IsBasicOpen (breakpoints q) U) :
      ∃ (x : ℝ) (hx : x ∈ U), IsIso (F.presheaf.germ U x hx) ∧
        (MeetsClosed (intervalSet q K) U ↔ x ∈ intervalSet q K) ∧ Epi (δ.hom.app (op U)) := by
    obtain ⟨x, hx, hxs⟩ := exists_mem_inter_subset hU
    have hg := isIso_germ_of_isConstructible hF hU hx hxs
    refine ⟨x, hx, hg, ⟨fun hm => ?_, fun h => ⟨hrel, ⟨x, hx, h⟩⟩⟩, ?_⟩
    · by_contra hn
      obtain ⟨y, hy, hyK⟩ := hm.2
      let G := (extension k hq).obj (interval _ K)
      have := isIso_germ_of_isConstructible hG hU hx hxs
      have := isIso_germ_extension_interval k hq K hU.2.1 hrel hy hyK
      have hz' := (isZero_stalk_extension_interval k hq hn).of_iso
        ((asIso (G.presheaf.germ U y hy)).symm ≪≫ asIso (G.presheaf.germ U x hx))
      obtain ⟨ey⟩ := nonempty_stalk_extension_interval_iso k hq hyK
      exact zero_ne_one ((ModuleCat.isZero_iff_subsingleton.1 (hz'.of_iso ey.symm)).elim
        (0 : k) (1 : k))
    · let st := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
        TopCat.Presheaf.stalkFunctor (X := realLine) (ModuleCat k) x
      have hepi : Epi δ := ⟨fun _ _ he => Cofork.IsColimit.hom_ext hc he⟩
      have hst : Epi (st.map δ) := st.map_epi δ
      have hBg : IsIso (B.presheaf.germ U x hx) :=
        isIso_germ_of_isConstructible hB hU hx hxs
      apply (epi_comp_iff_of_isIso _ (F.presheaf.germ U x hx)).mp
      rw [← TopCat.Presheaf.stalkFunctor_map_germ U x hx δ.hom]
      change Epi (B.presheaf.germ U x hx ≫ st.map δ)
      exact epi_comp' (IsIso.epi_of_iso _) hst
  refine nonempty_iso_extension_interval_of_sections hq F K ?_ ?_ ?_
  · intro U hU h
    obtain ⟨x, hx, hg, hmem, _⟩ := sectionsAt hU
    obtain ⟨ex⟩ := nonempty_iso_stalk_H1T_interval (k := k) hp _ hε (hK ▸ hmem.mp h)
    exact ⟨asIso (F.presheaf.germ U x hx) ≪≫ ex⟩
  · intro U hU h
    obtain ⟨x, hx, hg, hmem, _⟩ := sectionsAt hU
    have hz : IsZero (F.presheaf.stalk x) :=
      isZero_stalk_H1T_interval hp _ hε (fun hx => h (hmem.mpr (hK.symm ▸ hx)))
    exact hz.of_iso (asIso (F.presheaf.germ U x hx))
  · intro V U h hV hU hv hu
    obtain ⟨x, hx, hxK⟩ := hv.2
    have hwin : x ∈ Set.Icc (p j - ε) (p i + ε) := by
      rw [show intervalSet q K = _ from hK, hJ, outSet1_Ioo hε (hp hij)] at hxK
      exact hxK
    have hL : x ∈ outSet0 ε (intervalSet p (endpoint i)) := by
      rw [hl, outSet0_singleton hε]
      exact ⟨by linarith [hwin.1, hp hij], hwin.2⟩
    have hR : x ∈ outSet0 ε (intervalSet p (endpoint j)) := by
      rw [hr, outSet0_singleton hε]
      exact ⟨hwin.1, by linarith [hwin.2, hp hij]⟩
    have := isIso_H0T_restriction_of_mem (k := k) hp (endpoint i) hε (hl.symm ▸ isClosed_singleton)
      h hV.2.1 hU.2.1 ⟨hx, hL⟩
    have := isIso_H0T_restriction_of_mem (k := k) hp (endpoint j) hε (hr.symm ▸ isClosed_singleton)
      h hV.2.1 hU.2.1 ⟨hx, hR⟩
    -- Restriction on the endpoint pair induces a surjection on its one-dimensional quotient.
    have hi := isIso_section_restriction_biprod (A := L) (B := R) h
    let f := F.presheaf.map (homOfLE h).op
    have hiB : IsIso (B.presheaf.map (homOfLE h).op) := by
      let ev (W : Opens realLine) := TopCat.Sheaf.forget (ModuleCat k) realLine ⋙
        (evaluation _ _).obj (op W)
      let eU := (ev U).mapIso e
      let eV := (ev V).mapIso e
      have he : IsIso (B.presheaf.map (homOfLE h).op ≫ eV.hom) := by
        change IsIso (B.presheaf.map (homOfLE h).op ≫ e.hom.hom.app (op V))
        rw [e.hom.hom.naturality]
        exact IsIso.comp_isIso' eU.isIso_hom hi
      exact @IsIso.of_isIso_comp_right (ModuleCat k) _ _ _ _ _ eV.hom eV.isIso_hom he
    obtain ⟨xU, hxU, hgU, hmemU, _⟩ := sectionsAt hU
    obtain ⟨xV, hxV, hgV, hmemV, hδV⟩ := sectionsAt hV
    have hn := δ.hom.naturality (homOfLE h).op
    have : Epi (δ.hom.app (op U) ≫ f) := hn ▸
      epi_comp' (IsIso.epi_of_iso (B.presheaf.map (homOfLE h).op)) hδV
    have hf : Epi f := epi_of_epi (δ.hom.app (op U)) f
    obtain ⟨eU⟩ := nonempty_iso_stalk_H1T_interval (k := k) hp _ hε (hK ▸ hmemU.mp hu)
    obtain ⟨eV⟩ := nonempty_iso_stalk_H1T_interval (k := k) hp _ hε (hK ▸ hmemV.mp hv)
    let eu := asIso (F.presheaf.germ U xU hxU) ≪≫ eU
    let ev := asIso (F.presheaf.germ V xV hxV) ≪≫ eV
    have := eu.toLinearEquiv.symm.finiteDimensional
    have := ev.toLinearEquiv.symm.finiteDimensional
    have hs := (ModuleCat.epi_iff_surjective f).mp hf
    exact (ConcreteCategory.isIso_iff_bijective f).2
      ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (eu.toLinearEquiv.finrank_eq.trans ev.toLinearEquiv.finrank_eq.symm)).2 hs, hs⟩

/-- A nonempty degree-one output yields an interval sheaf on the shifted stratification. -/
theorem exists_intervalSheaf_H1T (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {ε : ℝ} (hε : 0 ≤ ε) (hne : (outSet1 ε (intervalSet p J)).Nonempty) :
    ∃ K : FiniteInterval (2 * (bandBreakpoints p ε).card + 1),
      intervalSet (sortedBreakpoints (bandBreakpoints p ε)) K = outSet1 ε (intervalSet p J) ∧
        Nonempty ((H[k,ε,1]).obj ((extension k hp).obj (interval _ J)) ≅
          (extension k (strictMono_sortedBreakpoints _)).obj (interval _ K)) := by
  obtain ⟨K, hK⟩ := exists_intervalSet_outSet1 hp J hε hne
  exact ⟨K, hK, nonempty_iso_H1T_interval_shifted hp J hε hne K hK⟩

/-- Degree-one convolution is isomorphic to the interval sheaf of any realization of its
output set. -/
theorem nonempty_iso_H1T_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {q : Fin n → ℝ} (hq : StrictMono q)
    (K : FiniteInterval (2 * n + 1)) (hK : intervalSet q K = outSet1 ε (intervalSet p J)) :
    Nonempty ((H[k,ε,1]).obj ((extension k hp).obj (interval _ J)) ≅
      (extension k hq).obj (interval _ K)) := by
  have hn : (outSet1 ε (intervalSet p J)).Nonempty := by
    rw [← hK]
    let v : Fin (2 * n + 1) := ⟨K.birth, K.birth_lt_death.trans_le K.death_le_size⟩
    obtain ⟨x, hx⟩ := stratum_nonempty hq v
    exact ⟨x, (mem_intervalSet_iff_alive hx).2 ⟨le_rfl, K.birth_lt_death⟩⟩
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_intervalSheaf_H1T (k := k) hp J hε hn
  let r := sortedBreakpoints (bandBreakpoints p ε)
  let h := strictMono_sortedBreakpoints (bandBreakpoints p ε)
  have heq : intervalSet r L = intervalSet q K := hL.trans hK.symm
  let G := (extension k h).obj (interval _ L)
  have good {U : Opens realLine} :
      MeetsClosed (intervalSet q K) U ↔ MeetsClosed (intervalSet r L) U := by rw [heq]
  obtain ⟨e'⟩ := nonempty_iso_extension_interval_of_sections hq G K
    (fun U hU hs => by
      obtain ⟨x, hx, hxI⟩ := (good.mp hs).2
      have := isIso_germ_extension_interval k h L hU.2.1 (good.mp hs).1 hx hxI
      exact ⟨asIso (G.presheaf.germ U x hx) ≪≫
        (nonempty_stalk_extension_interval_iso k h hxI).some⟩)
    (fun U hU hs => isZero_sections_extension_interval k h L hU.2.1 (mt good.mpr hs))
    (fun {_ _} _ hV hU hv hu => by
      obtain ⟨x, hx, hxI⟩ := (good.mp hv).2
      exact isIso_map_extension_interval k h L _ hV.2.1 hU.2.1
        (good.mp hv).1 (good.mp hu).1 hx hxI)
  exact ⟨e ≪≫ e'⟩

/-- Degree-one convolution of an interval sheaf is constructible for the shifted breakpoints. -/
theorem isConstructible_H1T_interval (hp : StrictMono p) (J : FiniteInterval (2 * m + 1))
    {ε : ℝ} (hε : 0 ≤ ε) :
    IsConstructible (bandBreakpoints p ε) ((H[k,ε,1]).obj
      ((extension k hp).obj (interval _ J))) := by
  rw [← breakpoints_sortedBreakpoints (bandBreakpoints p ε)]
  rcases (outSet1 ε (intervalSet p J)).eq_empty_or_nonempty with he | hn
  · exact isConstructible_of_isZero k (strictMono_sortedBreakpoints _)
      (isZero_H1T_interval hp J hε he)
  · obtain ⟨_, _, ⟨e⟩⟩ := exists_intervalSheaf_H1T (k := k) hp J hε hn
    exact isConstructible_of_iso e.symm
      (isConstructible_extension k (strictMono_sortedBreakpoints _) fun _ => inferInstance)

/-- Convolution of an interval sheaf has constructible cohomology for the shifted breakpoints. -/
theorem hasConstructibleCohomology_T_interval (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {ε : ℝ} (hε : 0 ≤ ε) :
    HasConstructibleCohomology k (sortedBreakpoints (bandBreakpoints p ε))
      (Plus.ι.obj ((T k ε).obj ((Plus.singleFunctor _ 0).obj
        ((extension k hp).obj (interval _ J))))) := by
  intro d
  rcases eq_or_ne d 0 with rfl | h₀
  · rw [breakpoints_sortedBreakpoints]
    exact isConstructible_H0T_interval hp J hε
  rcases eq_or_ne d 1 with rfl | h₁
  · rw [breakpoints_sortedBreakpoints]
    exact isConstructible_H1T_interval hp J hε
  exact isConstructible_of_isZero k (strictMono_sortedBreakpoints _)
    (isZero_homology_T_single ε hε _ d (by omega))

/-- Convolution of a constructible sheaf placed in degree zero has constructible cohomology
for the shifted breakpoints. -/
theorem hasConstructibleCohomology_T (hp : StrictMono p) {ε : ℝ} (hε : 0 ≤ ε)
    {F : realLine.Sheaf (ModuleCat k)} (hF : IsConstructible (breakpoints p) F) :
    HasConstructibleCohomology k (sortedBreakpoints (bandBreakpoints p ε))
      (Plus.ι.obj ((T k ε).obj ((Plus.singleFunctor _ 0).obj F))) := by
  let M := (sections k p).obj F
  have (v : Paths (Vertex (orient m))) := finiteDimensional_sections k hp hF v
  obtain ⟨xs, ⟨e⟩⟩ := exists_decomposition (orient m) M
  let eF : F ≅ intervalSheafSum k hp xs :=
    (sectionsExtensionIso k hp).app ⟨F, hF⟩ ≪≫
      (extension k hp).mapIso e ≪≫ extensionIntervalSumIso k hp xs
  intro d
  let G := H[k,ε,d]
  have := preservesBinaryBiproducts_of_preservesBiproducts G
  refine isConstructible_of_iso (G.mapIso eF).symm ?_
  clear eF e
  induction xs with
  | nil =>
    exact isConstructible_of_isZero k (strictMono_sortedBreakpoints _)
      (G.map_isZero (isZero_zero _))
  | cons J xs ih =>
    exact isConstructible_of_iso (G.mapBiprod _ _).symm
      (isConstructible_biprod (strictMono_sortedBreakpoints _)
        (hasConstructibleCohomology_T_interval hp J hε d) ih)

/-- Degree-one fibre cohomology has coefficient module `k` at every centre in the
degree-one output set. -/
theorem nonempty_iso_fibreCohomology_one_interval (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {ε y : ℝ} (hε : 0 ≤ ε)
    (hy : y ∈ outSet1 ε (intervalSet p J)) :
    Nonempty ((fibreCohomology k ε y ((extension k hp).obj (interval _ J)) 1).presheaf.stalk
      (PUnit.unit : pt) ≅ ModuleCat.of k k) := by
  obtain ⟨e⟩ := nonempty_iso_stalk_H1T_interval (k := k) hp J hε hy
  obtain ⟨ey⟩ := nonempty_iso_stalk_T_fibre (y := y) hε
    ((extension k hp).obj (interval _ J)) 1
  exact ⟨ey.symm ≪≫ e⟩

end Triangle

section ThresholdAugmentation

variable [HasDerivedCategory (realLine.Sheaf (ModuleCat k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat k))]

private theorem endpoint_aug_comp_ne_zero
    (hp : StrictMono p) {i j : Fin m} (hij : i < j)
    {ε : ℝ} (hε : 0 ≤ ε) (h : 2 * ε = p j - p i) :
    let S := (endpointSequence (k := k) hij).map (extension k hp)
    let hS := (endpointSequence_shortExact (k := k) hij).map_of_exact (extension k hp)
    (aug k hε).app ((Plus.singleFunctor _ 0).obj S.X₃) ≫
      (singleTrianglePlus hS).mor₃ ≠ 0 := by
  let C := realLine.Sheaf (ModuleCat k)
  let E := extension k hp
  let A := closedSegment hij
  let L := endpoint i
  let P := Plus.singleFunctor C 0
  let H₀ := Plus.homologyFunctor C 0
  let S := (endpointSequence (k := k) hij).map E
  let hS := (endpointSequence_shortExact (k := k) hij).map_of_exact E
  let tr := singleTrianglePlus hS
  let Bₗ := interval (k := k) (orient m) L
  let Bᵣ := interval (k := k) (orient m) (endpoint j)
  let F := E.obj Bₗ
  let inl : Bₗ ⟶ Bₗ ⊞ Bᵣ := biprod.inl
  let fst : Bₗ ⊞ Bᵣ ⟶ Bₗ := biprod.fst
  let ι : F ⟶ S.X₃ := E.map inl
  let π : S.X₃ ⟶ F := E.map fst
  let θ := aug k hε
  have hL : intervalSet p L = {p i} := intervalSet_eq_singleton hp rfl rfl
  have hA : intervalSet p A = Set.Icc (p i) (p j) := intervalSet_eq_Icc hp rfl rfl
  have hout : outSet0 ε (intervalSet p L) = Set.Icc (p i - ε) (p i + ε) := by
    rw [hL, outSet0_singleton hε]
  have hne : H0Aug k hε F ≠ 0 := (H0Aug_interval_ne_zero_iff hε hp L).2 (by
    rw [hout, hL]
    exact ⟨p i, ⟨by linarith, by linarith⟩, rfl⟩)
  change θ.app (P.obj S.X₃) ≫ tr.mor₃ ≠ 0
  intro hz
  -- A zero composite would lift the left endpoint augmentation to the closed interval.
  have hz' : (θ.app (P.obj F) ≫ P.map ι) ≫ tr.mor₃ = 0 := by
    have hn : (T k ε).map (P.map ι) ≫ θ.app (P.obj S.X₃) = θ.app (P.obj F) ≫ P.map ι :=
      θ.naturality (P.map ι)
    exact (congrArg (· ≫ tr.mor₃) hn.symm).trans
      ((Category.assoc _ _ _).trans (hz ▸ comp_zero))
  obtain ⟨u, hu⟩ := tr.coyoneda_exact₃ (singleTrianglePlus_distinguished hS) _ hz'
  let e₀ : H₀.obj tr.obj₂ ≅ S.X₂ :=
    (singleFunctorCompHomologyFunctorIsoPlus C 0).app S.X₂
  let f : H₀.obj ((T k ε).obj (P.obj F)) ⟶ S.X₂ := H₀.map u ≫ e₀.hom
  obtain ⟨K, hK, ⟨eK⟩⟩ := exists_intervalSheaf_H0T (k := k) hp L hε (by
    rw [hout]
    exact Set.nonempty_Icc.mpr (by linarith))
  let hq := strictMono_sortedBreakpoints (bandBreakpoints p ε)
  -- The right endpoint of the closed interval lies outside the convolved left endpoint.
  have hvan : eK.inv ≫ f = 0 :=
    hom_extension_interval_eq_zero_of_not_subset hq hp
      (by rw [hK, hout]; exact isClosed_Icc)
      (by rw [hA]; exact isClosed_Icc)
      (by
        rw [hA, hK, hout]
        intro hsub
        have hb := hsub (show p j ∈ Set.Icc (p i) (p j) from ⟨(hp hij).le, le_rfl⟩)
        linarith [hb.2, hp hij]) _
  have hf' : f = 0 := (cancel_epi eK.inv).mp (hvan.trans comp_zero.symm)
  have hf : H₀.map u = 0 := (cancel_mono e₀.hom).mp (hf'.trans zero_comp.symm)
  have hiπ : ι ≫ π = 𝟙 F :=
    (E.map_comp inl fst).symm.trans
      ((congrArg E.map (biprod.inl_fst : inl ≫ fst = 𝟙 Bₗ)).trans (E.map_id Bₗ))
  have hpaste : θ.app (P.obj F) = u ≫ tr.mor₂ ≫ P.map π := by
    have hh := congrArg (· ≫ P.map π) hu
    calc
      θ.app (P.obj F) = (θ.app (P.obj F) ≫ P.map ι) ≫ P.map π := by
        rw [Category.assoc, ← P.map_comp, hiπ, P.map_id]
        exact (Category.comp_id _).symm
      _ = _ := hh.trans (Category.assoc _ _ _)
  apply hne
  have hm : H₀.map (θ.app (P.obj F)) = 0 :=
    (congrArg H₀.map hpaste).trans (by rw [H₀.map_comp, hf, zero_comp])
  exact (congrArg (· ≫ (singleFunctorCompHomologyFunctorIsoPlus C 0).hom.app F) hm).trans
    zero_comp

private theorem app_ne_zero_of_comp_shift {C : Type*} [Category C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    {T : C ⥤ C} [T.CommShift ℤ] (θ : T ⟶ 𝟭 C) [θ.CommShift ℤ]
    {M N : C} (δ : N ⟶ M⟦(1 : ℤ)⟧) (h : θ.app N ≫ δ ≠ 0) : θ.app M ≠ 0 := by
  intro hz
  have hs := θ.app_shift (1 : ℤ) M
  simp only [hz, Functor.map_zero, zero_comp, comp_zero] at hs
  have hn : T.map δ ≫ θ.app (M⟦(1 : ℤ)⟧) = θ.app N ≫ δ := θ.naturality δ
  exact h (hn.symm.trans (hs ▸ comp_zero))

/-- At half the length of a bounded open interval, the augmentation is nonzero in `D⁺`. -/
theorem aug_interval_Ioo_threshold_ne_zero (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {a b ε : ℝ} (hε : 0 ≤ ε)
    (hab : a < b) (h : 2 * ε = b - a) (hJ : intervalSet p J = Set.Ioo a b) :
    (aug k hε).app ((Plus.singleFunctor _ 0).obj ((extension k hp).obj (interval _ J))) ≠ 0 := by
  have hout : (outSet1 ε (intervalSet p J)).Nonempty := by
    rw [hJ, outSet1_Ioo_threshold hε hab h]
    exact Set.singleton_nonempty _
  obtain ⟨i, j, hij, hends⟩ := exists_open_endpoints hp J hout
  have he := hends.symm.trans hJ
  have ha : p i = a := by
    simpa only [csInf_Ioo (hp hij), csInf_Ioo hab] using congrArg sInf he
  have hb : p j = b := by
    simpa only [csSup_Ioo (hp hij), csSup_Ioo hab] using congrArg sSup he
  have hJ' : J = openSegment hij := by
    apply eq_of_alive_iff
    intro v
    obtain ⟨x, hx⟩ := stratum_nonempty hp v
    rw [← mem_intervalSet_iff_alive hx, ← mem_intervalSet_iff_alive hx, hends,
      intervalSet_eq_Ioo hp (J := openSegment hij) rfl rfl]
  subst J
  let hS := (endpointSequence_shortExact (k := k) hij).map_of_exact (extension k hp)
  let tr := singleTrianglePlus hS
  have hcomp : (aug k hε).app tr.obj₃ ≫ tr.mor₃ ≠ 0 :=
    endpoint_aug_comp_ne_zero (k := k) hp hij hε (by rw [ha, hb]; exact h)
  have hθ := aug_commShift k hε
  exact app_ne_zero_of_comp_shift (aug k hε) tr.mor₃ hcomp

/-- Every cohomology sheaf map of the threshold augmentation is zero. -/
theorem homologyFunctor_map_aug_interval_Ioo_threshold (hp : StrictMono p)
    (J : FiniteInterval (2 * m + 1)) {a b ε : ℝ} (hε : 0 ≤ ε)
    (hab : a < b) (h : 2 * ε = b - a) (hJ : intervalSet p J = Set.Ioo a b) (i : ℤ) :
    (Plus.homologyFunctor _ i).map
      ((aug k hε).app ((Plus.singleFunctor _ 0).obj ((extension k hp).obj (interval _ J)))) =
      0 := by
  let F := (extension k hp).obj (interval _ J)
  let X := (Plus.singleFunctor (realLine.Sheaf (ModuleCat k)) 0).obj F
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact (Plus.isZero_homology_of_isGE X 0 i hi).eq_of_tgt _ _
  · have he : outSet0 ε (intervalSet p J) = ∅ := by
      rw [hJ, outSet0_Ioo hε hab, Set.Ioo_eq_empty_of_le (by linarith)]
    exact (isZero_H0T_interval hp J hε he).eq_of_src _ _
  · exact (Plus.isZero_homology_of_isLE X 0 i hi).eq_of_tgt _ _

end ThresholdAugmentation

end TDA.Sheaf.BandConvolution
