import TDA.Sheaf.AlternatingSourceReflection
import TDA.Persistence.FiniteDecomposition
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Interval decomposition of finite alternating diagrams

Every diagram of finite-dimensional vector spaces on an oriented path is isomorphic to a finite
biproduct of interval diagrams, and the multiset of intervals is determined by the isomorphism
class of the diagram.

Existence inducts on the weight `∑_{o a = false} (n - a)` of the backward arrows and, for a
fixed orientation, on the total dimension. At a source `p` just after the last backward arrow,
either a vector in the common kernel of the outgoing maps splits off the singleton interval
`{p}`, or the outgoing maps are jointly injective; then the diagram is the sink reflection of
its source reflection, whose orientation has smaller weight. For the all-forward orientation
the diagram is a finite persistence module on `Fin (n + 1)` and the existing decomposition
`TDA.Persistence.exists_list_interval_decomposition` applies through the path/order comparison
`chainToDiagram`.

Uniqueness inducts on the weight `∑_{o a = false} (a + 1)`. The sink reflection at the vertex
of the first backward arrow is an additive functor; it carries an interval sum to the interval
sum of the reflected intervals, reflection of intervals is invertible away from `{p}`, and the
number of copies of `{p}` is recovered from the dimension at `p`. The all-forward case is
`TDA.Persistence.barcode_decomposition_unique`.
-/

universe u

namespace TDA.Sheaf.AlternatingDiagram

open CategoryTheory Limits TDA.Persistence
open ZeroObject

variable {n : ℕ} {k : Type u} [Field k]

/-! ### Reversing the arrows at a vertex -/

/-- The orientation that reverses the arrows at `p`. -/
def flipAt (o : Fin n → Bool) (p : Fin (n + 1)) : Fin n → Bool :=
  fun a => if a.castSucc = p ∨ a.succ = p then !o a else o a

theorem src_tgt_cases (o : Fin n → Bool) (a : Fin n) :
    (src o a = a.castSucc ∧ tgt o a = a.succ) ∨ (src o a = a.succ ∧ tgt o a = a.castSucc) := by
  unfold src tgt
  cases o a <;> simp

theorem src_flipAt (o : Fin n → Bool) (p : Fin (n + 1)) (a : Fin n) :
    src (flipAt o p) a = if a.castSucc = p ∨ a.succ = p then tgt o a else src o a := by
  unfold src tgt flipAt
  split_ifs <;> simp_all

theorem tgt_flipAt (o : Fin n → Bool) (p : Fin (n + 1)) (a : Fin n) :
    tgt (flipAt o p) a = if a.castSucc = p ∨ a.succ = p then src o a else tgt o a := by
  unfold src tgt flipAt
  split_ifs <;> simp_all

theorem isFlipAt_flipAt (o : Fin n → Bool) (p : Fin (n + 1)) : IsFlipAt o (flipAt o p) p := by
  intro i j
  constructor
  · rintro ⟨a, hi, hj⟩
    rw [src_flipAt] at hi
    rw [tgt_flipAt] at hj
    by_cases ha : a.castSucc = p ∨ a.succ = p
    · rw [if_pos ha] at hi hj
      have hij : i = p ∨ j = p := by
        rcases src_tgt_cases o a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases ha with ha | ha <;> simp_all
      rw [if_pos hij]
      exact ⟨a, hj, hi⟩
    · rw [if_neg ha] at hi hj
      have hij : ¬ (i = p ∨ j = p) := by
        rcases src_tgt_cases o a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← hi, ← hj] <;>
          simp_all
      rw [if_neg hij]
      exact ⟨a, hi, hj⟩
  · intro h
    by_cases hij : i = p ∨ j = p
    · rw [if_pos hij] at h
      obtain ⟨a, hj, hi⟩ := h
      have ha : a.castSucc = p ∨ a.succ = p := by
        rcases src_tgt_cases o a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hij with hij | hij <;>
          subst hij <;> simp_all
      exact ⟨a, by rw [src_flipAt, if_pos ha, hi], by rw [tgt_flipAt, if_pos ha, hj]⟩
    · rw [if_neg hij] at h
      obtain ⟨a, hi, hj⟩ := h
      have ha : ¬ (a.castSucc = p ∨ a.succ = p) := by
        rcases src_tgt_cases o a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← hi, ← hj] at hij <;>
          simp_all
      exact ⟨a, by rw [src_flipAt, if_neg ha, hi], by rw [tgt_flipAt, if_neg ha, hj]⟩

/-! ### Weights of the backward arrows -/

/-- The weight used for existence: backward arrows weigh more the further left they are. -/
def weightE (o : Fin n → Bool) : ℕ := ∑ a : Fin n, if o a then 0 else n - a.val

/-- The weight used for uniqueness: backward arrows weigh more the further right they are. -/
def weightU (o : Fin n → Bool) : ℕ := ∑ a : Fin n, if o a then 0 else a.val + 1

theorem sum_two_points {f g : Fin n → ℕ} (a b : Fin n) (hab : a ≠ b)
    (h : ∀ c, c ≠ a → c ≠ b → f c = g c) :
    (∑ c, f c) + g a + g b = (∑ c, g c) + f a + f b := by
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ hb,
    ← Finset.add_sum_erase _ g (Finset.mem_univ a), ← Finset.add_sum_erase _ g hb,
    Finset.sum_congr rfl (fun c hc => h c (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc))
      (Finset.ne_of_mem_erase hc))]
  ring

theorem sum_one_point {f g : Fin n → ℕ} (a : Fin n) (h : ∀ c, c ≠ a → f c = g c) :
    (∑ c, f c) + g a = (∑ c, g c) + f a := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    ← Finset.add_sum_erase _ g (Finset.mem_univ a),
    Finset.sum_congr rfl (fun c hc => h c (Finset.ne_of_mem_erase hc))]
  ring

/-- An orientation with a backward arrow has a source, just after its last backward arrow,
whose reversal lowers `weightE`. -/
theorem exists_source_step (o : Fin n → Bool) (h : ∃ a, o a = false) :
    ∃ p : Fin (n + 1), IsSource o p ∧ weightE (flipAt o p) < weightE o := by
  classical
  let S := Finset.univ.filter (fun a : Fin n => o a = false)
  have hS : S.Nonempty := by obtain ⟨a, ha⟩ := h; exact ⟨a, by simp [S, ha]⟩
  let a := S.max' hS
  have ha : o a = false := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have hmax : ∀ b : Fin n, a < b → o b = true := by
    intro b hb
    by_contra hb'
    have : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hb'⟩
    exact absurd (S.le_max' b this) (not_le.mpr hb)
  refine ⟨a.succ, ?_, ?_⟩
  · rintro i ⟨b, -, hb⟩
    unfold tgt at hb
    cases hob : o b
    · rw [hob] at hb
      simp only [Bool.false_eq_true, ite_false] at hb
      have : a < b := by rw [Fin.lt_def]; have := congrArg Fin.val hb; simp at this; omega
      exact absurd (hmax b this) (by simp [hob])
    · rw [hob] at hb
      simp only [ite_true] at hb
      have : b = a := Fin.succ_injective _ hb
      rw [this, ha] at hob
      exact Bool.false_ne_true hob
  · let f : Fin n → ℕ := fun c => if o c then 0 else n - c.val
    let g : Fin n → ℕ := fun c => if flipAt o a.succ c then 0 else n - c.val
    have hga : g a = 0 := by simp [g, flipAt, ha]
    have hfa : f a = n - a.val := by simp [f, ha]
    have hpos : 0 < n - a.val := by have := a.isLt; omega
    change ∑ c, g c < ∑ c, f c
    by_cases hlast : a.val + 1 < n
    · let b : Fin n := ⟨a.val + 1, hlast⟩
      have hab : a ≠ b := fun h => by have := congrArg Fin.val h; simp [b] at this
      have hob : o b = true := hmax b (by rw [Fin.lt_def]; simp [b])
      have hbc : b.castSucc = a.succ := Fin.ext (by simp [b])
      have hfb : f b = 0 := by simp [f, hob]
      have hgb : g b = n - (a.val + 1) := by simp [g, flipAt, hbc, hob, b]
      have key := sum_two_points (f := f) (g := g) a b hab (fun c hca hcb => by
        have h1 : ¬ (c.castSucc = a.succ ∨ c.succ = a.succ) := by
          rintro (h1 | h1)
          · exact hcb (Fin.ext (by have := congrArg Fin.val h1; simp at this; simp [b]; omega))
          · exact hca (Fin.succ_injective _ h1)
        have hflip : flipAt o a.succ c = o c := by unfold flipAt; rw [if_neg h1]
        simp only [f, g, hflip])
      rw [hga, hfa, hfb, hgb] at key
      omega
    · have key := sum_one_point (f := f) (g := g) a (fun c hca => by
        have h1 : ¬ (c.castSucc = a.succ ∨ c.succ = a.succ) := by
          rintro (h1 | h1)
          · have := congrArg Fin.val h1; simp at this; have := c.isLt; omega
          · exact hca (Fin.succ_injective _ h1)
        have hflip : flipAt o a.succ c = o c := by unfold flipAt; rw [if_neg h1]
        simp only [f, g, hflip])
      rw [hga, hfa] at key
      omega

/-- An orientation with a backward arrow has a sink, at its first backward arrow, whose
reversal lowers `weightU`. -/
theorem exists_sink_step (o : Fin n → Bool) (h : ∃ a, o a = false) :
    ∃ p : Fin (n + 1), IsSink o p ∧ weightU (flipAt o p) < weightU o := by
  classical
  let S := Finset.univ.filter (fun a : Fin n => o a = false)
  have hS : S.Nonempty := by obtain ⟨a, ha⟩ := h; exact ⟨a, by simp [S, ha]⟩
  let a := S.min' hS
  have ha : o a = false := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hmin : ∀ b : Fin n, b < a → o b = true := by
    intro b hb
    by_contra hb'
    have : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hb'⟩
    exact absurd (S.min'_le b this) (not_le.mpr hb)
  refine ⟨a.castSucc, ?_, ?_⟩
  · rintro j ⟨b, hb, -⟩
    unfold src at hb
    cases hob : o b
    · rw [hob] at hb
      simp only [Bool.false_eq_true, ite_false] at hb
      have : b < a := by rw [Fin.lt_def]; have := congrArg Fin.val hb; simp at this; omega
      exact absurd (hmin b this) (by simp [hob])
    · rw [hob] at hb
      simp only [ite_true] at hb
      have : b = a := Fin.castSucc_injective _ hb
      rw [this, ha] at hob
      exact Bool.false_ne_true hob
  · let f : Fin n → ℕ := fun c => if o c then 0 else c.val + 1
    let g : Fin n → ℕ := fun c => if flipAt o a.castSucc c then 0 else c.val + 1
    have hga : g a = 0 := by simp [g, flipAt, ha]
    have hfa : f a = a.val + 1 := by simp [f, ha]
    change ∑ c, g c < ∑ c, f c
    by_cases hfirst : 0 < a.val
    · let b : Fin n := ⟨a.val - 1, by omega⟩
      have hab : a ≠ b := fun h => by have := congrArg Fin.val h; simp [b] at this; omega
      have hob : o b = true := hmin b (by rw [Fin.lt_def]; simp [b]; omega)
      have hbc : b.succ = a.castSucc := Fin.ext (by simp [b]; omega)
      have hfb : f b = 0 := by simp [f, hob]
      have hgb : g b = a.val := by
        have : ¬ b.castSucc = a.castSucc := fun h => hab (Fin.castSucc_injective _ h).symm
        simp [g, flipAt, hbc, hob, b]; omega
      have key := sum_two_points (f := f) (g := g) a b hab (fun c hca hcb => by
        have h1 : ¬ (c.castSucc = a.castSucc ∨ c.succ = a.castSucc) := by
          rintro (h1 | h1)
          · exact hca (Fin.castSucc_injective _ h1)
          · exact hcb (Fin.ext (by have := congrArg Fin.val h1; simp at this; simp [b]; omega))
        have hflip : flipAt o a.castSucc c = o c := by unfold flipAt; rw [if_neg h1]
        simp only [f, g, hflip])
      rw [hga, hfa, hfb, hgb] at key
      omega
    · have key := sum_one_point (f := f) (g := g) a (fun c hca => by
        have h1 : ¬ (c.castSucc = a.castSucc ∨ c.succ = a.castSucc) := by
          rintro (h1 | h1)
          · exact hca (Fin.castSucc_injective _ h1)
          · have := congrArg Fin.val h1; simp at this; omega
        have hflip : flipAt o a.castSucc c = o c := by unfold flipAt; rw [if_neg h1]
        simp only [f, g, hflip])
      rw [hga, hfa] at key
      omega

/-! ### The all-forward orientation and finite persistence modules -/

/-- The orientation with every arrow forward. -/
abbrev fwd (n : ℕ) : Fin n → Bool := fun _ => true

theorem arrow_fwd_le {i j : Fin (n + 1)} (h : Arrow (fwd n) i j) : i ≤ j := by
  obtain ⟨a, rfl, rfl⟩ := h
  simp only [src, tgt, ite_true]
  exact Fin.castSucc_le_succ a

theorem arrow_fwd_succ (a : Fin n) : Arrow (fwd n) a.castSucc a.succ :=
  ⟨a, by simp [src], by simp [tgt]⟩

/-- The path/order comparison: a persistence module on the chain `Fin (n + 1)` as a diagram on
the all-forward path, keeping the maps between consecutive indices. -/
noncomputable def chainToDiagram : PModule.{u,0,u} k (Fin (n + 1)) ⥤ Diagram k (fwd n) where
  obj G := ofArrows (fun j => G.obj j) (fun {_ _} h => G.map (homOfLE (arrow_fwd_le h)))
  map α := homMk (fun X => α.app (show Fin (n + 1) from X)) (fun h => by
    simp only [ofArrows_map_gen]
    exact α.naturality _)
  map_id G := by ext; rfl
  map_comp α β := by ext; rfl

instance chainToDiagram_additive : (chainToDiagram (k := k) (n := n)).Additive where
  map_add := by intros; ext; rfl

/-- A diagram on the all-forward path as a persistence module on `Fin (n + 1)`. -/
noncomputable def diagramToChain (M : Diagram k (fwd n)) : PModule.{u,0,u} k (Fin (n + 1)) :=
  ComposableArrows.mkOfObjOfMapSucc (fun j => M.obj (vtx _ j))
    (fun a => M.map (gen (arrow_fwd_succ a)))

instance diagramToChain_finiteDimensional (M : Diagram k (fwd n))
    [∀ X, FiniteDimensional k (M.obj X)] (i : Fin (n + 1)) :
    FiniteDimensional k ((diagramToChain M).obj i) :=
  inferInstanceAs (FiniteDimensional k (M.obj (vtx _ i)))

/-- A forward diagram is recovered from its persistence module. -/
noncomputable def isoChainToDiagram (M : Diagram k (fwd n)) :
    M ≅ chainToDiagram.obj (diagramToChain M) :=
  isoMk (fun _ => Iso.refl _) (fun {i j} h => by
    obtain ⟨a, rfl, rfl⟩ := h
    simp only [Iso.refl_hom]
    erw [Category.comp_id, Category.id_comp]
    exact (ComposableArrows.mkOfObjOfMapSucc_map_succ (C := ModuleCat.{u} k)
      (fun j => M.obj (vtx _ j)) (fun a => M.map (gen (arrow_fwd_succ a))) a.val a.isLt).symm)

/-- A persistence module is recovered from its forward diagram. -/
noncomputable def chainIso (G : PModule.{u,0,u} k (Fin (n + 1))) :
    diagramToChain (chainToDiagram.obj G) ≅ G :=
  ComposableArrows.isoMk (fun _ => Iso.refl _) (fun i hi => by
    simp only [Iso.refl_hom]
    erw [Category.comp_id, Category.id_comp]
    refine (ComposableArrows.mkOfObjOfMapSucc_map_succ (C := ModuleCat.{u} k) _ _ i hi).trans ?_
    simp only [chainToDiagram, ofArrows_map_gen]
    rfl)

/-- Isomorphic forward diagrams have isomorphic persistence modules. -/
noncomputable def diagramToChainIso {M N : Diagram k (fwd n)} (e : M ≅ N) :
    diagramToChain M ≅ diagramToChain N :=
  ComposableArrows.isoMk (fun i => e.app (vtx _ i)) (fun i hi => by
    unfold diagramToChain
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
    exact e.hom.naturality _)

/-- The chain interval module of `J` is the interval diagram of `J`. -/
noncomputable def intervalChainIso (J : FiniteInterval (n + 1)) :
    chainToDiagram.obj (intervalModule (k := k) J) ≅ interval (fwd n) J :=
  isoMk (fun _ => Iso.refl _) (fun {i j} h => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [chainToDiagram, interval, ofArrows_map_gen, Iso.refl_hom]
    exact (intervalMap_apply_val J (arrow_fwd_le h) x).trans (fiberMap_val J i j x).symm)

/-- The pointwise product of two persistence modules gives the biproduct of their diagrams. -/
noncomputable def pointwiseProdIsoBiprod (A B : PModule.{u,0,u} k (Fin (n + 1))) :
    chainToDiagram.obj (pointwiseProd A B) ≅ chainToDiagram.obj A ⊞ chainToDiagram.obj B := by
  let b : BinaryBicone (chainToDiagram.obj A) (chainToDiagram.obj B) :=
    { pt := chainToDiagram.obj (pointwiseProd A B)
      fst := homMk (fun X => ModuleCat.ofHom (LinearMap.fst k _ _)) (fun h => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl)
      snd := homMk (fun X => ModuleCat.ofHom (LinearMap.snd k _ _)) (fun h => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl)
      inl := homMk (fun X => ModuleCat.ofHom (LinearMap.inl k _ _)) (fun h => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        apply Prod.ext
        · rfl
        · exact (map_zero (B.map _).hom).symm)
      inr := homMk (fun X => ModuleCat.ofHom (LinearMap.inr k _ _)) (fun h => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        apply Prod.ext
        · exact (map_zero (A.map _).hom).symm
        · rfl)
      inl_fst := by ext; rfl
      inl_snd := by ext; rfl
      inr_fst := by ext; rfl
      inr_snd := by ext; rfl }
  refine (biprod.uniqueUpToIso _ _ (b := b) (isBinaryBilimitOfTotal b ?_))
  ext X x
  apply Prod.ext
  · change x.1 + 0 = x.1
    rw [add_zero]
  · change 0 + x.2 = x.2
    rw [zero_add]

/-- The forward diagram of a list barcode module is the interval sum of the list. -/
noncomputable def barcodeListIso : ∀ xs : List (FiniteInterval (n + 1)),
    chainToDiagram.obj (barcodeModuleOfList (k := k) xs) ≅ intervalSum (fwd n) xs
  | [] => by
    refine IsZero.iso ?_ (isZero_zero _)
    refine Functor.isZero _ fun X => ?_
    have : Subsingleton (∀ t : Fin ([] : List (FiniteInterval (n + 1))).length,
        (intervalModule (k := k) (([] : List (FiniteInterval (n + 1))).get t)).obj X) :=
      ⟨fun x y => funext fun t => t.elim0⟩
    exact ModuleCat.isZero_of_subsingleton (ModuleCat.of k _)
  | J :: xs => chainToDiagram.mapIso (barcodeModuleOfListConsIso J xs).symm ≪≫
      pointwiseProdIsoBiprod _ _ ≪≫ biprod.mapIso (intervalChainIso J) (barcodeListIso xs)

/-- Forward diagrams decompose, by the existing chain decomposition. -/
theorem exists_decomposition_fwd (M : Diagram k (fwd n)) [∀ X, FiniteDimensional k (M.obj X)] :
    ∃ xs : List (FiniteInterval (n + 1)), Nonempty (M ≅ intervalSum (fwd n) xs) := by
  obtain ⟨xs, ⟨e⟩⟩ := exists_list_interval_decomposition (diagramToChain M)
  exact ⟨xs, ⟨isoChainToDiagram M ≪≫ chainToDiagram.mapIso e ≪≫ barcodeListIso xs⟩⟩

/-- Forward interval sums determine their multisets, by the existing chain uniqueness. -/
theorem multiset_eq_of_iso_fwd {xs ys : List (FiniteInterval (n + 1))}
    (e : intervalSum (k := k) (fwd n) xs ≅ intervalSum (fwd n) ys) :
    (xs : Multiset (FiniteInterval (n + 1))) = ys := by
  let G := diagramToChain (intervalSum (k := k) (fwd n) xs)
  exact barcode_decomposition_unique G _ _
    (diagramToChainIso (barcodeListIso xs).symm ≪≫ chainIso _ ≪≫ barcodeModuleOfListIso xs)
    (diagramToChainIso (e ≪≫ (barcodeListIso ys).symm) ≪≫ chainIso _ ≪≫
      barcodeModuleOfListIso ys)

/-! ### Existence -/

/-- **Interval decomposition.** Every diagram of finite-dimensional vector spaces on an oriented
path is isomorphic to the biproduct of the interval diagrams of a finite list of intervals. -/
theorem exists_decomposition (o : Fin n → Bool) (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] :
    ∃ xs : List (FiniteInterval (n + 1)), Nonempty (M ≅ intervalSum o xs) := by
  suffices h : ∀ w (o : Fin n → Bool), weightE o = w → ∀ d (M : Diagram k o)
      [∀ X, FiniteDimensional k (M.obj X)], totalDim M = d →
      ∃ xs : List (FiniteInterval (n + 1)), Nonempty (M ≅ intervalSum o xs) from
    h _ o rfl _ M rfl
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ihw =>
  intro o hw d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro M _ hd
  by_cases hback : ∃ a, o a = false
  · obtain ⟨p, hs, hlt⟩ := exists_source_step o hback
    have hf := isFlipAt_flipAt o p
    by_cases hinj : OutInjective M p
    · obtain ⟨xs, ⟨e⟩⟩ := ihw _ (hw ▸ hlt) (flipAt o p) rfl _
        (reflectSource (flipAt o p) hs hf M) rfl
      exact ⟨_, ⟨reflectSourceUnitIso hs hf M hinj ≪≫
        (reflectSink o (hf.isSink hs) hf.symm).mapIso e ≪≫
        reflectSinkIntervalSumIso (hf.isSink hs) hf.symm xs⟩⟩
    · obtain ⟨N, _, ⟨e⟩, hN⟩ := exists_singleton_summand hs M hinj
      obtain ⟨ys, ⟨f⟩⟩ := ihd _ (hd ▸ hN) N rfl
      exact ⟨singletonInterval p :: ys, ⟨e ≪≫ biprod.mapIso (Iso.refl _) f⟩⟩
  · obtain rfl : o = fwd n := funext fun a => by
      cases h : o a
      · exact absurd ⟨a, h⟩ hback
      · rfl
    exact exists_decomposition_fwd M

/-! ### Uniqueness -/

theorem filterMap_reflectInterval_twice (p : Fin (n + 1)) (xs : List (FiniteInterval (n + 1))) :
    (xs.filterMap (reflectInterval p)).filterMap (reflectInterval p) =
      xs.filter (fun J => J ≠ singletonInterval p) := by
  induction xs with
  | nil => rfl
  | cons J xs ih =>
    cases hJ : reflectInterval p J with
    | none =>
      have : J = singletonInterval p := (reflectInterval_eq_none_iff p J).mp hJ
      rw [List.filterMap_cons_none hJ, ih, List.filter_cons_of_neg (by simp [this])]
    | some J' =>
      have hne : J ≠ singletonInterval p := fun h => by
        rw [h, reflectInterval_singleton] at hJ; simp at hJ
      rw [List.filterMap_cons_some hJ, List.filterMap_cons_some
        (reflectInterval_reflectInterval hJ), ih, List.filter_cons_of_pos (by simp [hne])]

/-- **Uniqueness of the decomposition.** Isomorphic interval sums have the same multiset of
intervals. -/
theorem multiset_eq_of_iso (o : Fin n → Bool) {xs ys : List (FiniteInterval (n + 1))}
    (e : intervalSum (k := k) o xs ≅ intervalSum o ys) :
    (xs : Multiset (FiniteInterval (n + 1))) = ys := by
  classical
  suffices h : ∀ w (o : Fin n → Bool), weightU o = w → ∀ {xs ys : List (FiniteInterval (n + 1))},
      (intervalSum (k := k) o xs ≅ intervalSum o ys) →
      (xs : Multiset (FiniteInterval (n + 1))) = ys from h _ o rfl e
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ihw =>
  intro o hw xs ys e
  by_cases hback : ∃ a, o a = false
  · obtain ⟨p, hs, hlt⟩ := exists_sink_step o hback
    have hf := isFlipAt_flipAt o p
    have hred := ihw _ (hw ▸ hlt) (flipAt o p) rfl
      ((reflectSinkIntervalSumIso hs hf xs).symm ≪≫ (reflectSink _ hs hf).mapIso e ≪≫
        reflectSinkIntervalSumIso hs hf ys)
    set s := singletonInterval p
    have hfilt : Multiset.filter (fun J => J ≠ s) (xs : Multiset _) =
        Multiset.filter (fun J => J ≠ s) (ys : Multiset _) := by
      have := congrArg (Multiset.filterMap (reflectInterval p)) hred
      simp only [Multiset.filterMap_coe, filterMap_reflectInterval_twice,
        Multiset.filter_coe] at this ⊢
      exact this
    have hdim := finrank_obj_eq_of_iso e (vtx o p)
    rw [finrank_intervalSum_obj, finrank_intervalSum_obj, ← Multiset.coe_countP,
      ← Multiset.coe_countP] at hdim
    have hsplit : ∀ zs : Multiset (FiniteInterval (n + 1)),
        Multiset.countP (fun J => J.alive p) zs =
          Multiset.countP (fun J => J.alive p) (Multiset.filter (fun J => J ≠ s) zs) +
            Multiset.count s zs := by
      intro zs
      conv_lhs => rw [← Multiset.filter_add_not (fun J => J ≠ s) zs]
      rw [Multiset.countP_add, Multiset.count_eq_card_filter_eq]
      congr 1
      rw [Multiset.countP_eq_card.mpr]
      · congr 1
        exact Multiset.filter_congr fun J _ => by simp [eq_comm]
      · intro J hJ
        have : J = s := by simpa using (Multiset.mem_filter.mp hJ).2
        subst this
        simp [s, singletonInterval, FiniteInterval.alive]
    have hcount : Multiset.count s (xs : Multiset _) = Multiset.count s (ys : Multiset _) := by
      have h1 := hsplit xs
      have h2 := hsplit ys
      rw [hfilt] at h1
      omega
    rw [← Multiset.filter_add_not (fun J => J = s) (xs : Multiset _),
      ← Multiset.filter_add_not (fun J => J = s) (ys : Multiset _),
      Multiset.filter_eq', Multiset.filter_eq', hcount]
    congr 1
  · obtain rfl : o = fwd n := funext fun a => by
      cases h : o a
      · exact absurd ⟨a, h⟩ hback
      · rfl
    exact multiset_eq_of_iso_fwd e

/-! ### The barcode of a diagram -/

/-- The barcode of a finite-dimensional diagram: the multiset of intervals of any interval
decomposition. -/
noncomputable def barcode {o : Fin n → Bool} (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] : Multiset (FiniteInterval (n + 1)) :=
  ((exists_decomposition o M).choose : Multiset (FiniteInterval (n + 1)))

/-- A chosen, noncanonical isomorphism of a diagram with the biproduct of its barcode. -/
noncomputable def barcodeIso {o : Fin n → Bool} (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] : M ≅ barcodeDiagram o (barcode M) :=
  (exists_decomposition o M).choose_spec.some ≪≫ intervalSumIsoBarcodeDiagram _

/-- Isomorphic barcode diagrams have equal barcodes. -/
theorem eq_of_iso_barcodeDiagram {o : Fin n → Bool} {B C : Multiset (FiniteInterval (n + 1))}
    (e : barcodeDiagram (k := k) o B ≅ barcodeDiagram o C) : B = C := by
  have := multiset_eq_of_iso o e
  rwa [Multiset.coe_toList, Multiset.coe_toList] at this

/-- Any decomposition of a diagram has the barcode as its multiset of intervals. -/
theorem barcode_eq_of_iso {o : Fin n → Bool} (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] {B : Multiset (FiniteInterval (n + 1))}
    (e : M ≅ barcodeDiagram o B) : barcode M = B :=
  eq_of_iso_barcodeDiagram ((barcodeIso M).symm ≪≫ e)

/-- The barcode of a list decomposition is its multiset. -/
theorem barcode_eq_of_iso_intervalSum {o : Fin n → Bool} (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] {xs : List (FiniteInterval (n + 1))}
    (e : M ≅ intervalSum o xs) : barcode M = xs :=
  barcode_eq_of_iso M (e ≪≫ intervalSumIsoBarcodeDiagram xs)

theorem barcode_intervalSum (o : Fin n → Bool) (xs : List (FiniteInterval (n + 1))) :
    barcode (intervalSum (k := k) o xs) = xs :=
  barcode_eq_of_iso_intervalSum _ (Iso.refl _)

theorem barcode_barcodeDiagram (o : Fin n → Bool) (B : Multiset (FiniteInterval (n + 1))) :
    barcode (barcodeDiagram (k := k) o B) = B :=
  barcode_eq_of_iso _ (Iso.refl _)

/-- Isomorphic diagrams have equal barcodes. -/
theorem barcode_eq_of_iso' {o : Fin n → Bool} {M N : Diagram k o}
    [∀ X, FiniteDimensional k (M.obj X)] [∀ X, FiniteDimensional k (N.obj X)] (e : M ≅ N) :
    barcode M = barcode N :=
  barcode_eq_of_iso M (e ≪≫ barcodeIso N)

/-- **Classification.** Finite-dimensional diagrams are isomorphic exactly when their barcodes,
equivalently their interval multiplicities, agree. -/
theorem nonempty_iso_iff_barcode_eq {o : Fin n → Bool} (M N : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] [∀ X, FiniteDimensional k (N.obj X)] :
    Nonempty (M ≅ N) ↔ barcode M = barcode N := by
  constructor
  · rintro ⟨e⟩; exact barcode_eq_of_iso' e
  · intro h
    exact ⟨barcodeIso M ≪≫ eqToIso (congrArg (barcodeDiagram o) h) ≪≫ (barcodeIso N).symm⟩

/-- The multiplicity of an interval in a diagram: an isomorphism invariant. -/
noncomputable def intervalMultiplicity {o : Fin n → Bool} (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] (J : FiniteInterval (n + 1)) : ℕ :=
  (barcode M).count J

theorem intervalMultiplicity_eq_of_iso {o : Fin n → Bool} {M N : Diagram k o}
    [∀ X, FiniteDimensional k (M.obj X)] [∀ X, FiniteDimensional k (N.obj X)] (e : M ≅ N)
    (J : FiniteInterval (n + 1)) : intervalMultiplicity M J = intervalMultiplicity N J := by
  unfold intervalMultiplicity; rw [barcode_eq_of_iso' e]

/-- The dimension at a vertex counts the bars containing it. -/
theorem finrank_obj_eq_countP_barcode {o : Fin n → Bool} (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] (j : Fin (n + 1)) :
    Module.finrank k (M.obj (vtx o j)) = (barcode M).countP (fun J => J.alive j) := by
  rw [finrank_obj_eq_of_iso (barcodeIso M), barcodeDiagram, finrank_intervalSum_obj,
    ← Multiset.coe_countP, Multiset.coe_toList]

/-- A zero diagram has the empty barcode. -/
theorem barcode_eq_zero_of_isZero {o : Fin n → Bool} (M : Diagram k o)
    [∀ X, FiniteDimensional k (M.obj X)] (hM : IsZero M) : barcode M = 0 :=
  barcode_eq_of_iso_intervalSum M (hM.iso (isZero_zero _))

end TDA.Sheaf.AlternatingDiagram
