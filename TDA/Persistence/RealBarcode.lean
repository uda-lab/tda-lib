import TDA.Persistence.IndexDiagram
import TDA.Persistence.Constructible
import TDA.Persistence.RankReindex

/-!
# Real half-open interval modules and finite barcode realization

An endpoint pair `(b,d)` supports the real parameters `b ≤ t < d`, where `d = ⊤`
allows an essential tail. Finite products are indexed by occurrences, so repeated pairs
give separate coordinates. On positive pairs this is the interval-module convention of
Bauer--Lesnick, arXiv:1311.3681v4, §§2.1--2.3. Empty supports are permitted by the
constructor; the finite-constructible application uses positive endpoint pairs.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.RealBarcode

open CategoryTheory

variable {k : Type u} [Field k]

/-- The left endpoint is included and the finite right endpoint is excluded. -/
def alive (p : ℝ × WithTop ℝ) (t : ℝ) : Prop := p.1 ≤ t ∧ (t : WithTop ℝ) < p.2

/-- The full coefficient field on the support and its zero submodule elsewhere. -/
noncomputable def fiber (p : ℝ × WithTop ℝ) (t : ℝ) : Submodule k k := by
  classical
  exact if alive p t then ⊤ else ⊥

private theorem alive_middle (p : ℝ × WithTop ℝ) {s t r : ℝ}
    (hst : s ≤ t) (htr : t ≤ r) (hs : alive p s) (hr : alive p r) : alive p t :=
  ⟨hs.1.trans hst, lt_of_le_of_lt (WithTop.coe_le_coe.mpr htr) hr.2⟩

private noncomputable def intervalMap (p : ℝ × WithTop ℝ) {s t : ℝ} (_h : s ≤ t) :
    fiber (k := k) p s →ₗ[k] fiber (k := k) p t := by
  classical
  exact if h : alive p s ∧ alive p t then
    Submodule.inclusion (by simp [fiber, h.1, h.2]) else 0

/-- The standard real half-open interval module, including infinite right endpoints. -/
noncomputable def intervalModule (p : ℝ × WithTop ℝ) : PModule.{u,0,u} k ℝ where
  obj t := ModuleCat.of k (fiber (k := k) p t)
  map f := ModuleCat.ofHom (intervalMap p (leOfHom f))
  map_id t := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change fiber (k := k) p t at x
    change intervalMap (k := k) p (leOfHom (𝟙 t)) x = x
    apply Subtype.ext
    by_cases h : alive p t
    · simp [intervalMap, h]
    · have hx : (x : k) = 0 := by
        simpa only [fiber, if_neg h, Submodule.mem_bot] using x.property
      simp [intervalMap, h, hx]
  map_comp {s t r} f g := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases hs : alive p s
    · by_cases hr : alive p r
      · have ht := alive_middle p (leOfHom f) (leOfHom g) hs hr
        simp [intervalMap, hs, ht, hr]
      · simp [intervalMap, hr]
    · simp [intervalMap, hs]

private noncomputable def productModule {ι : Type} (F : ι → PModule.{u,0,u} k ℝ) :
    PModule.{u,0,u} k ℝ where
  obj t := ModuleCat.of k (∀ i, (F i).obj t)
  map f := ModuleCat.ofHom (LinearMap.piMap (fun i => ((F i).map f).hom))
  map_id t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    simp [LinearMap.piMap]
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    simp [LinearMap.piMap, Functor.map_comp]

-- The only coordinate change used below: reindex occurrences, then apply the supplied
-- natural isomorphism in each coordinate. This does not identify repeated values.
private noncomputable def productIso {ι κ : Type} (e : ι ≃ κ)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (η : ∀ j, F (e.symm j) ≅ G j) : productModule F ≅ productModule G := by
  refine NatIso.ofComponents (fun t =>
    ((LinearEquiv.piCongrLeft' k (fun i => (F i).obj t) e).trans
      (LinearEquiv.piCongrRight (fun j => ((η j).app t).toLinearEquiv))).toModuleIso) ?_
  intro s t f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext j
  exact congrArg (fun L => L.hom (x (e.symm j))) ((η j).hom.naturality f)

/-- The coordinate product used by barcode realizations, indexed by occurrences. -/
noncomputable def familyModule {ι : Type} (F : ι → PModule.{u,0,u} k ℝ) :
    PModule.{u,0,u} k ℝ := productModule F

/-- Reindex occurrence coordinates and apply the supplied natural isomorphism in
each coordinate. -/
noncomputable def familyIso {ι κ : Type} (e : ι ≃ κ)
    (F : ι → PModule.{u,0,u} k ℝ) (G : κ → PModule.{u,0,u} k ℝ)
    (η : ∀ j, F (e.symm j) ≅ G j) : familyModule F ≅ familyModule G :=
  productIso e F G η

/-- A list enumeration of a finite real barcode, with one coordinate per occurrence. -/
noncomputable def ofList (xs : List (ℝ × WithTop ℝ)) : PModule.{u,0,u} k ℝ :=
  productModule (fun i : Fin xs.length => intervalModule (k := k) (xs.get i))

/-- The real module associated to a diagram's endpoint multiset.
Positive pairs give nonempty half-open intervals; multiplicity is retained. -/
noncomputable def realize (D : Diagram ℝ) : PModule.{u,0,u} k ℝ :=
  ofList D.points.toList

/-- Finite endpoint multisets have finite-dimensional realization fibers. -/
instance realize_finiteDimensional (D : Diagram ℝ) (t : ℝ) :
    FiniteDimensional k ((realize (k := k) D).obj t) := by
  change FiniteDimensional k (∀ i : Fin D.points.toList.length,
    fiber (k := k) (D.points.toList.get i) t)
  infer_instance

/-- An empty endpoint multiset realizes the zero module. -/
theorem realize_isZero_of_points_eq_zero (D : Diagram ℝ) (h : D.points = 0) :
    CategoryTheory.Limits.IsZero (realize (k := k) D) := by
  apply Functor.isZero
  intro t
  have hlen : D.points.toList.length = 0 := by simp [h]
  have : Subsingleton ((realize (k := k) D).obj t) := by
    change Subsingleton (∀ i : Fin D.points.toList.length,
      fiber (k := k) (D.points.toList.get i) t)
    refine ⟨fun x y => funext (fun i => ?_)⟩
    have hi := i.isLt
    omega
  exact ModuleCat.isZero_of_subsingleton _

private noncomputable def permutationEquiv {xs ys : List (ℝ × WithTop ℝ)}
    (h : xs.Perm ys) : Fin xs.length ≃ Fin ys.length := by
  classical
  letI : BEq (ℝ × WithTop ℝ) := ⟨fun x y => decide (x = y)⟩
  letI : LawfulBEq (ℝ × WithTop ℝ) := inferInstance
  exact ⟨h.idxBij, h.symm.idxBij, h.idxBij_symm_leftInverse_idxBij,
    h.symm.idxBij_symm_leftInverse_idxBij⟩

/-- Reordering a real barcode changes its realization by a coordinate natural isomorphism. -/
noncomputable def enumerationIso {xs ys : List (ℝ × WithTop ℝ)} (h : xs.Perm ys) :
    ofList (k := k) xs ≅ ofList (k := k) ys := by
  classical
  letI : BEq (ℝ × WithTop ℝ) := ⟨fun x y => decide (x = y)⟩
  letI : LawfulBEq (ℝ × WithTop ℝ) := inferInstance
  let e := permutationEquiv h
  apply productIso e
  intro j
  have hp : ys.get j = xs.get (e.symm j) := by
    have hp := h.getElem_idxBij_eq_getElem (e.symm j)
    change ys.get (e (e.symm j)) = xs.get (e.symm j) at hp
    simpa using hp
  exact eqToIso (congrArg (intervalModule (k := k)) hp.symm)

variable {n : ℕ}

/-- Real endpoints of a finite interval on the unpadded critical grid.
Death at the grid size gives the constant essential tail. -/
def endpoints (c : Fin n ↪o ℝ) (I : FiniteInterval n) : ℝ × WithTop ℝ :=
  (c ⟨I.birth, by have := I.birth_lt_death; have := I.death_le_size; omega⟩,
    if hd : I.death < n then (c ⟨I.death, hd⟩ : WithTop ℝ) else ⊤)

/-- This endpoint conversion is definitionally the existing `ofIndexBars` convention. -/
theorem ofIndexBars_points (c : Fin n ↪o ℝ) (B : Multiset (FiniteInterval n)) :
    (ofIndexBars c c.strictMono B).points = B.map (endpoints c) := rfl

/-- Remove the initial zero index from an interval which is known not to start there. -/
def dropZero (I : FiniteInterval (n + 1)) (hb : 0 < I.birth) : FiniteInterval n where
  birth := I.birth - 1
  death := I.death - 1
  birth_lt_death := by have := I.birth_lt_death; omega
  death_le_size := by have := I.death_le_size; omega

/-- The endpoint cut for sampling at `1,...,n` subtracts one from positive endpoints. -/
theorem sampledEndpoint_succ (e : ℕ) (he : 0 < e) (hen : e ≤ n + 1) :
    sampledEndpoint (Fin.succOrderEmb n).toOrderHom e = e - 1 := by
  unfold sampledEndpoint
  have hset : Finset.univ.filter (fun i : Fin n => ((Fin.succOrderEmb n) i).val < e) =
      Finset.univ.filter (fun i : Fin n => i.val < e - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change i.val + 1 < e ↔ i.val < e - 1
    omega
  change (Finset.univ.filter (fun i : Fin n => ((Fin.succOrderEmb n) i).val < e)).card = e - 1
  rw [hset, Fin.card_filter_val_lt, Nat.min_eq_right (by omega)]

/-- No positive-birth interval is discarded by `Fin.succ` sampling. -/
theorem restrictAlong_succ (I : FiniteInterval (n + 1)) (hb : 0 < I.birth) :
    I.restrictAlong (Fin.succOrderEmb n).toOrderHom = some (dropZero I hb) := by
  have hd : 0 < I.death := hb.trans I.birth_lt_death
  have hbn : I.birth ≤ n + 1 := Nat.le_trans (Nat.le_of_lt I.birth_lt_death) I.death_le_size
  simp only [FiniteInterval.restrictAlong, sampledEndpoint_succ I.birth hb hbn,
    sampledEndpoint_succ I.death hd I.death_le_size]
  have hlt : I.birth - 1 < I.death - 1 := by have := I.birth_lt_death; omega
  simp only [dif_pos hlt]
  rfl

private theorem critical_le_iff (c : Fin n ↪o ℝ) (i : Fin n) (t : ℝ) :
    c i ≤ t ↔ i.val + 1 ≤ (FiniteConstructible.cellIndex c t).val := by
  rw [← FiniteConstructible.lt_cellIndex_iff]
  omega

private theorem lt_critical_iff (c : Fin n ↪o ℝ) (i : Fin n) (t : ℝ) :
    t < c i ↔ (FiniteConstructible.cellIndex c t).val ≤ i.val := by
  rw [← not_le, critical_le_iff]
  omega

/-- Pulling back a positive-birth index interval gives exactly its real half-open support. -/
theorem alive_endpoints_dropZero (c : Fin n ↪o ℝ)
    (I : FiniteInterval (n + 1)) (hb : 0 < I.birth) (t : ℝ) :
    alive (endpoints c (dropZero I hb)) t ↔
      I.alive (FiniteConstructible.cellIndex c t) := by
  have hbd := I.birth_lt_death
  have hdn := I.death_le_size
  have hq := (FiniteConstructible.cellIndex c t).isLt
  dsimp only [alive, endpoints, dropZero, FiniteInterval.alive]
  split_ifs with hd
  · rw [WithTop.coe_lt_coe, critical_le_iff, lt_critical_iff]
    dsimp only
    omega
  · simp only [WithTop.coe_lt_top, and_true]
    rw [critical_le_iff]
    dsimp only
    omega

/-- The real support identification respects maps, not only dimensions or ranks. -/
noncomputable def intervalPullbackIso (c : Fin n ↪o ℝ)
    (I : FiniteInterval (n + 1)) (hb : 0 < I.birth) :
    reindex (FiniteConstructible.cellIndex c) (TDA.Persistence.intervalModule (k := k) I) ≅
      intervalModule (k := k) (endpoints c (dropZero I hb)) := by
  classical
  have hf (t : ℝ) : FiniteInterval.fiber (k := k) I (FiniteConstructible.cellIndex c t) =
      fiber (k := k) (endpoints c (dropZero I hb)) t := by
    simp only [FiniteInterval.fiber, fiber, alive_endpoints_dropZero]
  let e (t : ℝ) := LinearEquiv.ofEq _ _ (hf t)
  refine NatIso.ofComponents (fun t => (e t).toModuleIso) ?_
  intro s t f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change FiniteInterval.fiber (k := k) I (FiniteConstructible.cellIndex c s) at x
  change e t (TDA.Persistence.intervalMap (k := k) I
    ((FiniteConstructible.cellIndex c).monotone (leOfHom f)) x) =
      intervalMap (k := k) (endpoints c (dropZero I hb)) (leOfHom f) (e s x)
  apply Subtype.ext
  by_cases hs : I.alive (FiniteConstructible.cellIndex c s) <;>
    by_cases ht : I.alive (FiniteConstructible.cellIndex c t) <;>
    simp [e, intervalMap, TDA.Persistence.intervalMap, alive_endpoints_dropZero, hs, ht,
      LinearEquiv.coe_ofEq_apply]

/-- A finite death becomes the corresponding critical value, not infinity. -/
theorem endpoints_dropZero_finite (c : Fin n ↪o ℝ)
    (I : FiniteInterval (n + 1)) (hb : 0 < I.birth) (hd : I.death ≤ n) :
    (endpoints c (dropZero I hb)).2 =
      (c ⟨I.death - 1, by have := I.birth_lt_death; omega⟩ : WithTop ℝ) := by
  have hlt : I.death - 1 < n := by have := I.birth_lt_death; omega
  simp [endpoints, dropZero, hlt]

/-- Survival past the last finite stage becomes an essential right tail. -/
theorem endpoints_dropZero_essential (c : Fin n ↪o ℝ)
    (I : FiniteInterval (n + 1)) (hb : 0 < I.birth) (hd : I.death = n + 1) :
    (endpoints c (dropZero I hb)).2 = ⊤ := by
  simp [endpoints, dropZero, hd]

/-- `Fin.succ` sampling retains every occurrence when no bar starts at zero. -/
theorem reindexBarcode_succ_card (B : Multiset (FiniteInterval (n + 1)))
    (hB : ∀ I ∈ B, 0 < I.birth) :
    (reindexBarcode (Fin.succOrderEmb n).toOrderHom B).card = B.card := by
  revert hB
  induction B using Multiset.induction_on with
  | empty => intro _; rfl
  | @cons I B ih =>
    intro hB
    have hI := hB I (Multiset.mem_cons_self I B)
    have htail : ∀ J ∈ B, 0 < J.birth := fun J hJ => hB J (Multiset.mem_cons_of_mem hJ)
    simp only [reindexBarcode, Multiset.filterMap_cons_some _ _ _ (restrictAlong_succ I hI),
      Multiset.card_cons]
    exact congrArg (· + 1) (ih htail)

private noncomputable def pointEnumeration (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval (n + 1))) (hB : ∀ I ∈ B, 0 < I.birth) :
    List (ℝ × WithTop ℝ) :=
  List.ofFn (fun i : Fin B.toList.length => endpoints c
    (dropZero (B.toList.get i) (hB _ (Multiset.mem_toList.mp (List.get_mem B.toList i)))))

-- Compare lists only after computing the filterMap. Because every option is
-- `some`, there is one output coordinate for every input coordinate, including duplicates.
private theorem pointEnumeration_points (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval (n + 1))) (hB : ∀ I ∈ B, 0 < I.birth) :
    (ofIndexBars c c.strictMono (reindexBarcode (Fin.succOrderEmb n).toOrderHom B)).points =
      (pointEnumeration c B hB : Multiset _) := by
  let f (I : FiniteInterval (n + 1)) :=
    (I.restrictAlong (Fin.succOrderEmb n).toOrderHom).map (endpoints c)
  let p (i : Fin B.toList.length) := endpoints c
    (dropZero (B.toList.get i) (hB _ (Multiset.mem_toList.mp (List.get_mem B.toList i))))
  have hf (i : Fin B.toList.length) : f (B.toList.get i) = some (p i) := by
    dsimp [f, p]
    rw [restrictAlong_succ]
    rfl
  have hlist : B.toList.filterMap f = List.ofFn p := by
    calc
      B.toList.filterMap f = (List.finRange B.toList.length).filterMap
          (fun i => f (B.toList.get i)) := by
        conv_lhs => rw [← List.ofFn_get B.toList, List.ofFn_eq_map]
        rw [List.filterMap_map]
        rfl
      _ = (List.finRange B.toList.length).map p :=
        List.filterMap_eq_map_iff_forall_eq_some.mpr (fun i _ => hf i)
      _ = List.ofFn p := List.ofFn_eq_map.symm
  rw [ofIndexBars_points, reindexBarcode, Multiset.map_filterMap]
  change Multiset.filterMap f B = (List.ofFn p : Multiset _)
  calc
    Multiset.filterMap f B = Multiset.filterMap f (B.toList : Multiset _) :=
      congrArg (Multiset.filterMap f) (Multiset.coe_toList B).symm
    _ = (B.toList.filterMap f : Multiset _) := rfl
    _ = (List.ofFn p : Multiset _) := congrArg (fun xs : List (ℝ × WithTop ℝ) => (xs : Multiset (ℝ × WithTop ℝ))) hlist

private noncomputable def ofFnIso {m : ℕ} (p : Fin m → ℝ × WithTop ℝ) :
    productModule (fun i => intervalModule (k := k) (p i)) ≅ ofList (List.ofFn p) := by
  let e : Fin m ≃ Fin (List.ofFn p).length := (finCongr (List.length_ofFn (f := p))).symm
  apply productIso e
  intro j
  apply eqToIso
  apply congrArg (intervalModule (k := k))
  rw [List.get_ofFn]
  apply congrArg p
  exact Fin.ext rfl

/-- The pulled-back finite barcode is realized by exactly the existing endpoint diagram.
Every occurrence is transported, rather than collapsed to a set of distinct endpoints. -/
noncomputable def barcodePullbackIso (c : Fin n ↪o ℝ)
    (B : Multiset (FiniteInterval (n + 1))) (hB : ∀ I ∈ B, 0 < I.birth) :
    reindex (FiniteConstructible.cellIndex c) (barcodeModule (k := k) B) ≅
      realize (ofIndexBars c c.strictMono (reindexBarcode (Fin.succOrderEmb n).toOrderHom B)) := by
  let p (i : Fin B.toList.length) := endpoints c
    (dropZero (B.toList.get i) (hB _ (Multiset.mem_toList.mp (List.get_mem B.toList i))))
  let F (i : Fin B.toList.length) :=
    reindex (FiniteConstructible.cellIndex c) (TDA.Persistence.intervalModule (k := k) (B.toList.get i))
  let G (i : Fin B.toList.length) := intervalModule (k := k) (p i)
  have ep : productModule F ≅ productModule G := productIso (Equiv.refl _) F G
    (fun i => intervalPullbackIso c (B.toList.get i)
      (hB _ (Multiset.mem_toList.mp (List.get_mem B.toList i))))
  have hperm : (List.ofFn p).Perm
      (ofIndexBars c c.strictMono (reindexBarcode (Fin.succOrderEmb n).toOrderHom B)).points.toList := by
    apply Multiset.coe_eq_coe.mp
    rw [Multiset.coe_toList, pointEnumeration_points c B hB]
    rfl
  change productModule F ≅ _
  exact ep ≪≫ ofFnIso p ≪≫ enumerationIso hperm

end TDA.Persistence.RealBarcode
