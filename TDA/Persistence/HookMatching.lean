import TDA.Persistence.FiniteRankProjectiveResolutionHookBetti
import TDA.Persistence.RectangleMatching

/-!
# Finite hook-sum bottleneck matchings

This module compares occurrence-indexed finite sums of the finite-death and
principal-upset hooks used in rank-projective resolutions. Occurrence labels
remain distinct when hook tags repeat. The finite-death significance criterion
below records the exact boundary behavior of a hook transition.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.HookMatching

open CategoryTheory CategoryTheory.Limits CoordinateShift
open scoped TDA.Persistence NNReal Classical ZeroObject

variable {k : Type u} [Field k] {n : ℕ}

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The module represented by a finite-death or principal-upset hook tag. -/
noncomputable def tagModule (t : RealHookTag (n := n)) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) t

/-- The occurrence-indexed finite biproduct represented by a family of hook
tags. Repeated tags remain separate summands. -/
noncomputable def familyModule {m : ℕ} (F : Fin m → RealHookTag (n := n)) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  ⨁ fun i => tagModule (k := k) (F i)

private instance (ε : ℝ≥0) : (shift (R := k) (n := n) ε).Additive where
  map_add := by intros; rfl

/-- The canonical inclusion of one hook occurrence into its finite sum. -/
noncomputable def inclusion {m : ℕ} (F : Fin m → RealHookTag (n := n)) (i : Fin m) :
    tagModule (k := k) (F i) ⟶ familyModule (k := k) F :=
  biproduct.ι (fun i : Fin m => tagModule (k := k) (F i)) i

/-- The canonical projection onto one hook occurrence. -/
noncomputable def projection {m : ℕ} (F : Fin m → RealHookTag (n := n)) (i : Fin m) :
    familyModule (k := k) F ⟶ tagModule (k := k) (F i) :=
  biproduct.π (fun i : Fin m => tagModule (k := k) (F i)) i

@[simp] theorem inclusion_projection_self {m : ℕ}
    (F : Fin m → RealHookTag (n := n)) (i : Fin m) :
    inclusion (k := k) F i ≫ projection F i = 𝟙 (tagModule (k := k) (F i)) :=
  biproduct.ι_π_self (fun j : Fin m => tagModule (k := k) (F j)) i

@[simp] theorem inclusion_projection_ne {m : ℕ}
    (F : Fin m → RealHookTag (n := n)) {i j : Fin m} (h : i ≠ j) :
    inclusion (k := k) F i ≫ projection F j = 0 :=
  biproduct.ι_π_ne (fun j : Fin m => tagModule (k := k) (F j)) h

theorem sum_projection_inclusion {m : ℕ} (F : Fin m → RealHookTag (n := n)) :
    ∑ i, projection (k := k) F i ≫ inclusion F i = 𝟙 (familyModule (k := k) F) :=
  biproduct.total (f := fun i : Fin m => tagModule (k := k) (F i))

/-- The `(i,j)` component of a shifted map of finite hook sums. -/
noncomputable def component {m ℓ : ℕ} (F : Fin m → RealHookTag (n := n))
    (G : Fin ℓ → RealHookTag (n := n)) (ε : ℝ≥0)
    (f : familyModule (k := k) F ⟶ (shift ε).obj (familyModule (k := k) G))
    (i : Fin m) (j : Fin ℓ) :
    tagModule (k := k) (F i) ⟶ (shift ε).obj (tagModule (k := k) (G j)) :=
  inclusion (k := k) F i ≫ f ≫ (shift ε).map (projection (k := k) G j)

/-- A composite between finite hook-sum matrices is the sum of its paths. -/
theorem component_composite {m ℓ q : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (H : Fin q → RealHookTag (n := n)) (ε : ℝ≥0)
    (f : familyModule (k := k) F ⟶ (shift ε).obj (familyModule (k := k) G))
    (g : familyModule (k := k) G ⟶ (shift ε).obj (familyModule (k := k) H))
    (i : Fin m) (l : Fin q) :
    ∑ j : Fin ℓ, component (k := k) F G ε f i j ≫
      (shift ε).map (component (k := k) G H ε g j l) =
      inclusion (k := k) F i ≫ f ≫ (shift ε).map g ≫
        (shift ε).map ((shift ε).map (projection (k := k) H l)) := by
  classical
  simp only [component, Functor.map_comp, Category.assoc]
  rw [← Preadditive.comp_sum]
  simp only [← Category.assoc]
  rw [← Preadditive.sum_comp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [← Preadditive.comp_sum]
  rw [← Functor.map_sum]
  have hs : (∑ a : Fin ℓ, projection (k := k) G a ≫ inclusion G a ≫ g) = g := by
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, sum_projection_inclusion, Category.id_comp]
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]

/-- The two maps of an interleaving give the actual finite sum of component
paths, with the diagonal and off-diagonal transitions kept distinct. -/
theorem component_interleaving_sum {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G)) (i i' : Fin m) :
    (∑ j : Fin ℓ, component (k := k) F G ε I.φ i j ≫
      (shift ε).map (component (k := k) G F ε I.ψ j i')) ≫
        (compIso ε ε (tagModule (k := k) (F i'))).hom =
      inclusion (k := k) F i ≫ transition (ε + ε) (familyModule (k := k) F) ≫
        (shift (ε + ε)).map (projection (k := k) F i') := by
  classical
  rw [component_composite]
  simp only [Category.assoc]
  rw [compIso_naturality ε ε (projection (k := k) F i')]
  simp only [← Category.assoc, I.φ_ψ]

theorem component_interleaving_sum_ne {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (ε : ℝ≥0) (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G)) {i i' : Fin m} (h : i ≠ i') :
    (∑ j : Fin ℓ, component (k := k) F G ε I.φ i j ≫
      (shift ε).map (component (k := k) G F ε I.ψ j i')) ≫
        (compIso ε ε (tagModule (k := k) (F i'))).hom = 0 := by
  rw [component_interleaving_sum F G ε I i i']
  simp only [← Category.assoc]
  rw [transition_naturality (ε + ε) (inclusion (k := k) F i)]
  simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_ne F h,
    Functor.map_zero, comp_zero]

theorem component_interleaving_sum_self {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (ε : ℝ≥0) (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G)) (i : Fin m) :
    (∑ j : Fin ℓ, component (k := k) F G ε I.φ i j ≫
      (shift ε).map (component (k := k) G F ε I.ψ j i)) ≫
        (compIso ε ε (tagModule (k := k) (F i))).hom =
      transition (ε + ε) (tagModule (k := k) (F i)) := by
  rw [component_interleaving_sum F G ε I i i]
  simp only [← Category.assoc]
  rw [transition_naturality (ε + ε) (inclusion (k := k) F i)]
  simp only [Category.assoc, ← Functor.map_comp, inclusion_projection_self]
  simp

/-- A partial occurrence matching of hook families records actual interleavings
for its pairs and for every deletion on either side. -/
structure IsMatching {m ℓ : ℕ} (ρ : ℝ≥0)
    (F : Fin m → RealHookTag (n := n))
    (G : Fin ℓ → RealHookTag (n := n))
    (M : OccurrenceMatching (Fin m) (Fin ℓ) PEmpty.{1} PEmpty.{1}) : Prop where
  paired : ∀ i j, M.finite i = some j →
    Nonempty (CoordinateInterleaving ρ (tagModule (k := k) (F i))
      (tagModule (k := k) (G j)))
  source_zero : ∀ i, M.finite i = none →
    Nonempty (CoordinateInterleaving ρ (tagModule (k := k) (F i)) 0)
  target_zero : ∀ j, (∀ i, M.finite i ≠ some j) →
    Nonempty (CoordinateInterleaving ρ (tagModule (k := k) (G j)) 0)

/-- An admissible edge records an actual interleaving, not just endpoint
closeness or a nonzero morphism. -/
def tagNeighbor (ρ : ℝ≥0) (t s : RealHookTag (n := n)) : Prop :=
  Nonempty (CoordinateInterleaving ρ (tagModule (k := k) t)
    (tagModule (k := k) s))

/-- A scalar order value used to triangularize each same-type Hall block. -/
def tagOrderValue (t : RealHookTag (n := n)) : ℝ :=
  match t with
  | .inl ab => (∑ i, ab.val.1 i) + ∑ i, ab.val.2 i
  | .inr a => ∑ i, a i

/-- The occurrence multiset has one entry for each family index. -/
theorem hookTagMultiset_card {m : ℕ}
    (F : Fin m → RealHookTag (n := n)) :
    Multiset.card (hookTagMultiset F) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [hookTagMultiset, ih]

/-- At zero interleaving distance, two finite hook sums have a matching by
equal hook tags, with every repeated occurrence retained. -/
theorem exists_matching_of_zero_interleaving {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n))
    (G : Fin ℓ → RealHookTag (n := n))
    (I : CoordinateInterleaving 0 (familyModule (k := k) F)
      (familyModule (k := k) G)) :
    ∃ M : OccurrenceMatching (Fin m) (Fin ℓ) PEmpty.{1} PEmpty.{1},
      IsMatching (k := k) 0 F G M := by
  classical
  let P : FiniteHookSumPresentation (k := k) (n := n)
      (familyModule (k := k) F) := ⟨m, F, Iso.refl _⟩
  let Q : FiniteHookSumPresentation (k := k) (n := n)
      (familyModule (k := k) G) := ⟨ℓ, G, Iso.refl _⟩
  have htags := P.tagMultiset_eq_of_iso Q I.toIso
  have hlen : m = ℓ := by
    have hc := congrArg Multiset.card htags
    simpa only [hookTagMultiset_card] using hc
  have hcard (c : RealHookTag (n := n)) :
      Fintype.card {i : Fin m // F i = c} =
        Fintype.card {j : Fin ℓ // G j = c} := by
    have hc := congrArg (fun s : Multiset (RealHookTag (n := n)) => s.count c) htags
    simpa only [hookTagMultiset_count] using hc
  let E : ∀ c : RealHookTag (n := n),
      {i : Fin m // F i = c} ≃ {j : Fin ℓ // G j = c} :=
    fun c => Fintype.equivOfCardEq (hcard c)
  let eF : Fin m ≃ Σ c : RealHookTag (n := n), {i : Fin m // F i = c} :=
    { toFun := fun i => ⟨F i, ⟨i, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := by intro i; rfl
      right_inv := by
        rintro ⟨c, ⟨i, hi⟩⟩
        cases hi
        rfl }
  let eG : Fin ℓ ≃ Σ c : RealHookTag (n := n), {j : Fin ℓ // G j = c} :=
    { toFun := fun j => ⟨G j, ⟨j, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := by intro j; rfl
      right_inv := by
        rintro ⟨c, ⟨j, hj⟩⟩
        cases hj
        rfl }
  let eFiber :
      (Σ c : RealHookTag (n := n), {i : Fin m // F i = c}) ≃
        (Σ c : RealHookTag (n := n), {j : Fin ℓ // G j = c}) :=
    { toFun := fun x => ⟨x.1, E x.1 x.2⟩
      invFun := fun y => ⟨y.1, (E y.1).symm y.2⟩
      left_inv := by intro x; cases x with | mk c i => simp
      right_inv := by intro y; cases y with | mk c j => simp }
  let e : Fin m ≃ Fin ℓ := eF.trans (eFiber.trans eG.symm)
  let σ : Fin m → Fin ℓ := e
  have hσtag (i : Fin m) : G (σ i) = F i := by
    have he := eG.apply_symm_apply (eFiber (eF i))
    change eG (σ i) = eFiber (eF i) at he
    exact congrArg Sigma.fst he
  have hσinj : Function.Injective σ := e.injective
  have hσsurj : Function.Surjective σ := e.surjective
  let M : OccurrenceMatching (Fin m) (Fin ℓ) PEmpty.{1} PEmpty.{1} :=
    ⟨fun i => some (σ i), (by
      intro i j q hi hj
      simp only [Option.some.injEq] at hi hj
      exact hσinj (hi.trans hj.symm)), Equiv.refl _⟩
  refine ⟨M, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hji : σ i = j := by simpa [M] using hij
    subst j
    exact ⟨CoordinateInterleaving.ofIso
      (eqToIso (congrArg (tagModule (k := k)) (hσtag i).symm))⟩
  · intro i hi
    simp [M] at hi
  · intro j hj
    obtain ⟨i, rfl⟩ := hσsurj j
    exact (hj i rfl).elim

/-- A finite-death endpoint pair, viewed as a hook summand in real coordinates. -/
abbrev FiniteHookTag :=
  FiniteHookDeflation.StrictPair (Fin n → ℝ)

/-- A nonzero map between shifted finite-death hooks forces the target birth
and death to lie below the corresponding translated source endpoints. This is
the endpoint input for the ordered-hook geometry in the matching proof. -/
theorem nonzero_finiteHook_map_endpoint_bounds {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d))
    (hf : f ≠ 0) :
    c ≤ CoordinateShift.translation ε a ∧
      d ≤ CoordinateShift.translation ε b := by
  classical
  let ha : a ∈ Hook.support a b := Hook.birth_mem hab
  let x : SupportInterval.fiber (k := k) (Hook.support a b) a :=
    SupportInterval.one (k := k) _ ha
  let y : SupportInterval.fiber (k := k) (Hook.support c d)
      (CoordinateShift.translation ε a) := (f.app a).hom x
  have hy : (y : k) ≠ 0 := by
    intro hy0
    apply hf
    apply Hook.hom_ext hab
    apply Subtype.ext
    exact hy0
  have htarget : CoordinateShift.translation ε a ∈ Hook.support c d := by
    by_contra hp
    exact hy (SupportInterval.val_eq_zero (Hook.support c d) hp y)
  have hdie := Hook.generator_dies (k := k) hab f
  have hpEnd : CoordinateShift.translation ε b ∉ Hook.support c d := by
    intro hp
    have hval := congrArg Subtype.val hdie
    change ((structureMapLinear
      (SupportInterval.module (k := k) (Hook.support c d)
        (Hook.support_ordConnected c d))
      ((CoordinateShift.translation ε).monotone' hab.le) y : k) = 0) at hval
    rw [SupportInterval.structureMap_val] at hval
    split_ifs at hval with hmem
    · exact hy hval
    · exact (hmem hp).elim
  exact ⟨htarget.1, by
    have hb : CoordinateShift.translation ε a ≤ CoordinateShift.translation ε b :=
      (CoordinateShift.translation ε).monotone' hab.le
    have hbirth : c ≤ CoordinateShift.translation ε b := htarget.1.trans hb
    by_contra hdb
    exact hpEnd ⟨hbirth, hdb⟩⟩

/-- A nonzero map out of a finite hook is already nonzero on its birth unit. -/
theorem finiteHook_map_birth_value_ne_zero {a b c d : Fin n → ℝ} (hab : a < b)
    (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) (hf : f ≠ 0) :
    (f.app a).hom (SupportInterval.one (Hook.support a b)
      (Hook.birth_mem hab)) ≠ 0 := by
  intro hz
  apply hf
  apply Hook.hom_ext hab
  rw [hz]
  simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- A nonzero hook map has an active target fiber at the translated birth. -/
theorem finiteHook_map_birth_active {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d))
    (hf : f ≠ 0) :
    CoordinateShift.translation ε a ∈ Hook.support c d := by
  let x := SupportInterval.one (k := k) (Hook.support a b) (Hook.birth_mem hab)
  let y : SupportInterval.fiber (k := k) (Hook.support c d)
      (CoordinateShift.translation ε a) := (f.app a).hom x
  have hy : y ≠ 0 := finiteHook_map_birth_value_ne_zero hab ε f hf
  by_contra h
  apply hy
  apply Subtype.ext
  exact SupportInterval.val_eq_zero (Hook.support c d) h y

/-- Naturality carries the nonzero birth coefficient of a hook map to any
comparable active overlap point. -/
theorem finiteHook_map_component_ne_zero {a b c d p : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d))
    (hf : f ≠ 0) (hap : a ≤ p) (hp : p ∈ Hook.support a b)
    (hpT : CoordinateShift.translation ε p ∈ Hook.support c d) :
    (f.app p).hom (SupportInterval.one (Hook.support a b) hp) ≠ 0 := by
  classical
  let ha : a ∈ Hook.support a b := Hook.birth_mem hab
  let x : SupportInterval.fiber (k := k) (Hook.support a b) a :=
    SupportInterval.one (k := k) (Hook.support a b) ha
  let x' : SupportInterval.fiber (k := k) (Hook.support a b) p :=
    SupportInterval.one (k := k) (Hook.support a b) hp
  have hbirth : (f.app a).hom x ≠ 0 :=
    finiteHook_map_birth_value_ne_zero hab ε f hf
  have hsrc : structureMapLinear (Hook.module (k := k) a b) hap x = x' := by
    apply Subtype.ext
    rw [SupportInterval.structureMap_val]
    simp [hp, x, x', SupportInterval.one]
  have hn := congrArg (fun z => z.hom x) (f.naturality (homOfLE hap))
  change (f.app p).hom (structureMapLinear
      (Hook.module (k := k) a b) hap x) =
    structureMapLinear ((CoordinateShift.shift ε).obj
      (Hook.module (k := k) c d)) hap ((f.app a).hom x) at hn
  rw [hsrc] at hn
  intro hz
  apply hbirth
  have hzero : structureMapLinear ((CoordinateShift.shift ε).obj
      (Hook.module (k := k) c d)) hap ((f.app a).hom x) = 0 := by
    rw [← hn, hz]
  apply Subtype.ext
  have hv := congrArg Subtype.val hzero
  change ((structureMapLinear
      (SupportInterval.module (k := k) (Hook.support c d)
        (Hook.support_ordConnected c d))
      ((CoordinateShift.translation ε).monotone' hap)
      ((f.app a).hom x) : k) = 0) at hv
  have hval := SupportInterval.structureMap_val (k := k) (S := Hook.support c d)
    (Hook.support_ordConnected c d) ((CoordinateShift.translation ε).monotone' hap)
    ((f.app a).hom x)
  rw [if_pos (show (CoordinateShift.translation ε).toFun p ∈ Hook.support c d from hpT)]
    at hval
  exact hval.symm.trans hv

/-- The scalar coefficient of a shifted finite-hook map is its value on the
source birth generator. -/
noncomputable def finiteHookCoefficient {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) : k :=
  ((show SupportInterval.fiber (k := k) (Hook.support c d)
      (CoordinateShift.translation ε a) from
    (f.app a).hom (SupportInterval.one (Hook.support a b)
      (Hook.birth_mem hab))) : k)

private theorem finiteHookCoefficient_zero_aux {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0) :
    finiteHookCoefficient (k := k) hab ε
      (0 : Hook.module (k := k) a b ⟶
        (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) = 0 := by
  unfold finiteHookCoefficient
  change (0 : k) = 0
  rfl

/-- Naturality identifies the birth coefficient with every supported component
of a finite-hook map. -/
theorem finiteHookCoefficient_eq_at {a b c d p : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d))
    (hap : a ≤ p) (hp : p ∈ Hook.support a b)
    (hpT : CoordinateShift.translation ε p ∈ Hook.support c d) :
    finiteHookCoefficient (k := k) hab ε f =
      ((show SupportInterval.fiber (k := k) (Hook.support c d)
        (CoordinateShift.translation ε p) from
        (f.app p).hom (SupportInterval.one (Hook.support a b) hp)) : k) := by
  classical
  let x := SupportInterval.one (k := k) (Hook.support a b) (Hook.birth_mem hab)
  have hn := congrArg (fun v =>
      ((show SupportInterval.fiber (k := k) (Hook.support c d)
        (CoordinateShift.translation ε p) from v.hom x) : k))
    (f.naturality (homOfLE hap))
  have hsrc : structureMapLinear (Hook.module (k := k) a b) hap x =
      SupportInterval.one (Hook.support a b) hp := by
    apply Subtype.ext
    rw [SupportInterval.structureMap_val]
    simp [hp, x, SupportInterval.one]
  change ((show SupportInterval.fiber (k := k) (Hook.support c d)
      (CoordinateShift.translation ε p) from
        (f.app p).hom (structureMapLinear (Hook.module (k := k) a b) hap x)) : k) =
    (structureMapLinear (Hook.module (k := k) c d)
      ((CoordinateShift.translation ε).monotone' hap) ((f.app a).hom x) : k) at hn
  rw [hsrc] at hn
  have hs := SupportInterval.structureMap_val (Hook.support c d)
    (Hook.support_ordConnected c d) ((CoordinateShift.translation ε).monotone' hap)
    ((f.app a).hom x)
  rw [if_pos (show (CoordinateShift.translation ε).toFun p ∈ Hook.support c d from hpT)] at hs
  change _ = finiteHookCoefficient (k := k) hab ε f at hs
  rw [hs] at hn
  exact hn.symm

/-- A finite-hook map is nonzero precisely when its birth coefficient is. -/
theorem finiteHookCoefficient_ne_zero_iff {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) :
    finiteHookCoefficient (k := k) hab ε f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · intro h hf
    subst f
    apply h
    change (0 : k) = 0
    rfl
  · intro hf hz
    have hbirth := finiteHook_map_birth_value_ne_zero hab ε f hf
    have hz' : ((show SupportInterval.fiber (k := k) (Hook.support c d)
        (CoordinateShift.translation ε a) from
      (f.app a).hom (SupportInterval.one (Hook.support a b)
        (Hook.birth_mem hab))) : k) = 0 := by
      simpa only [finiteHookCoefficient] using hz
    apply hbirth
    apply Subtype.ext
    exact hz'

/-- The coefficient of a shifted map between principal upsets, read at the
source birth when the target is active there. -/
noncomputable def principalHookCoefficient {a c : Fin n → ℝ} (ε : ℝ≥0)
    (f : HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) : k := by
  classical
  exact if h : c ≤ CoordinateShift.translation ε a then
    HookInfinity.fiberEquivOfLe (R := k) h ((f.app a).hom (HookInfinity.birth a))
  else 0

/-- A principal-upset map is nonzero precisely when its source birth has a
nonzero coefficient in an active target fiber. -/
theorem principalHookCoefficient_ne_zero_iff {a c : Fin n → ℝ} (ε : ℝ≥0)
    (f : HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) :
    principalHookCoefficient (k := k) ε f ≠ 0 ↔ f ≠ 0 := by
  classical
  constructor
  · intro h hf
    subst f
    have hzero : principalHookCoefficient (k := k) ε
        (0 : HookInfinity.module (R := k) a ⟶
          (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) = 0 := by
      unfold principalHookCoefficient
      split_ifs with hactive
      · change HookInfinity.fiberEquivOfLe (R := k) hactive
          (0 : (HookInfinity.module (R := k) c).obj (CoordinateShift.translation ε a)) = 0
        exact map_zero (HookInfinity.fiberEquivOfLe (R := k) hactive).toLinearMap
      · rfl
    exact h hzero
  · intro hf
    by_cases ha : c ≤ CoordinateShift.translation ε a
    · intro hzero
      have hscalar : HookInfinity.fiberEquivOfLe (R := k) ha
          ((f.app a).hom (HookInfinity.birth a)) = 0 := by
        simpa [principalHookCoefficient, ha] using hzero
      have hval : (f.app a).hom (HookInfinity.birth a) = 0 :=
        (HookInfinity.fiberEquivOfLe (R := k) ha).injective (by
          calc
            HookInfinity.fiberEquivOfLe (R := k) ha
                ((f.app a).hom (HookInfinity.birth a)) = 0 := hscalar
            _ = HookInfinity.fiberEquivOfLe (R := k) ha 0 :=
              (map_zero (HookInfinity.fiberEquivOfLe (R := k) ha).toLinearMap).symm)
      exact hf (HookInfinity.hom_ext hval)
    · intro hzero
      apply hf
      apply HookInfinity.hom_ext
      exact HookInfinity.fiber_eq_zero_of_not_le (R := k) ha
        ((f.app a).hom (HookInfinity.birth a))

@[simp] theorem principalHookCoefficient_zero {a c : Fin n → ℝ} (ε : ℝ≥0) :
    principalHookCoefficient (k := k) ε
      (0 : HookInfinity.module (R := k) a ⟶
        (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) = 0 := by
  classical
  unfold principalHookCoefficient
  split_ifs with h
  · simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply,
      CoordinateShift.shift_obj]
    exact map_zero (HookInfinity.fiberEquivOfLe (R := k) h).toLinearMap
  · rfl

theorem principalHookCoefficient_add {a c : Fin n → ℝ} (ε : ℝ≥0)
    (f g : HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) :
    principalHookCoefficient (k := k) ε (f + g) =
      principalHookCoefficient (k := k) ε f +
        principalHookCoefficient (k := k) ε g := by
  classical
  unfold principalHookCoefficient
  split_ifs with h
  · simp only [NatTrans.app_add, ModuleCat.hom_add, LinearMap.add_apply]
    exact (HookInfinity.fiberEquivOfLe (R := k) h).map_add _ _
  · simp

theorem principalHookCoefficient_sum {a c : Fin n → ℝ} {ι : Type*}
    (ε : ℝ≥0) (A : Finset ι)
    (f : ι → (HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c))) :
    principalHookCoefficient (k := k) ε (∑ i ∈ A, f i) =
      ∑ i ∈ A, principalHookCoefficient (k := k) ε (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih => simp [hi, principalHookCoefficient_add, ih]

/-- A scalar coordinate for same-type hook morphisms. Cross-type entries are
set to zero; their composites through the forbidden finite-to-principal map
vanish, so these are exactly the coefficients needed in the Hall matrices. -/
noncomputable def tagScalar (ε : ℝ≥0) (t s : RealHookTag (n := n))
    (f : tagModule (k := k) t ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) s)) : k :=
  match t, s with
  | .inl ab, .inl cd => finiteHookCoefficient (k := k) ab.property ε f
  | .inr a, .inr c => principalHookCoefficient (k := k) ε f
  | _, _ => 0

@[simp] private theorem tagScalar_zero (ε : ℝ≥0) (t s : RealHookTag (n := n)) :
    tagScalar (k := k) ε t s
      (0 : tagModule (k := k) t ⟶
        (CoordinateShift.shift ε).obj (tagModule (k := k) s)) = 0 := by
  cases t with
  | inl ab =>
    cases s with
    | inl cd =>
      change finiteHookCoefficient (k := k) ab.property ε
        (0 : Hook.module (k := k) ab.val.1 ab.val.2 ⟶
          (CoordinateShift.shift ε).obj
            (Hook.module (k := k) cd.val.1 cd.val.2)) = 0
      exact finiteHookCoefficient_zero_aux (k := k) ab.property ε
    | inr c => simp [tagScalar]
  | inr a =>
    cases s with
    | inl cd => simp [tagScalar]
    | inr c =>
      change principalHookCoefficient (k := k) ε
        (0 : HookInfinity.module (R := k) a ⟶
          (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) = 0
      exact principalHookCoefficient_zero (k := k) (a := a) (c := c) ε

private theorem principalHook_birth_span {a p : Fin n → ℝ} (hap : a ≤ p)
    (x : (HookInfinity.module (R := k) a).obj p) :
    x = (HookInfinity.fiberEquivOfLe (R := k) hap x) •
      structureMapLinear (HookInfinity.module (R := k) a) hap
        (HookInfinity.birth a) := by
  apply (HookInfinity.fiberEquivOfLe (R := k) hap).injective
  rw [map_smul, HookInfinity.fiberEquivOfLe_structureMap
    (R := k) (le_rfl : a ≤ a) hap]
  have hb : HookInfinity.fiberEquivOfLe (R := k)
      (show a ≤ a from le_rfl) (HookInfinity.birth a) = 1 := by
    change (HookInfinity.birth a).val () = 1
    simp [HookInfinity.birth, GradedFree.birth, GradedFree.generator]
  rw [hb]
  simp

/-- Coefficients multiply under composition of shifted principal-upset maps.
The activation inequalities are consequences of nonzero source and middle
maps, so no common grade is assumed. -/
theorem principalHookCoefficient_composite {a c e : Fin n → ℝ}
    (ε : ℝ≥0)
    (f : HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c))
    (g : HookInfinity.module (R := k) c ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) e)) :
    principalHookCoefficient (k := k) (ε + ε)
      (f ≫ (CoordinateShift.shift ε).map g ≫
        (CoordinateShift.compIso ε ε (HookInfinity.module (R := k) e)).hom) =
      principalHookCoefficient (k := k) ε f *
        principalHookCoefficient (k := k) ε g := by
  classical
  by_cases hfc : principalHookCoefficient (k := k) ε f = 0
  · have hf : f = 0 := by
      by_contra hne
      exact ((principalHookCoefficient_ne_zero_iff (k := k) ε f).2 hne) hfc
    simp [hf]
  by_cases hgc : principalHookCoefficient (k := k) ε g = 0
  · have hg : g = 0 := by
      by_contra hne
      exact ((principalHookCoefficient_ne_zero_iff (k := k) ε g).2 hne) hgc
    simp [hg]
  have hca : c ≤ CoordinateShift.translation ε a := by
    by_contra h
    exact hfc (by simp [principalHookCoefficient, h])
  have hec : e ≤ CoordinateShift.translation ε c := by
    by_contra h
    exact hgc (by simp [principalHookCoefficient, h])
  let q := CoordinateShift.translation ε a
  have hq : c ≤ q := hca
  have hmid : e ≤ CoordinateShift.translation ε q :=
    le_trans hec ((CoordinateShift.translation ε).monotone' hq)
  have hdouble : CoordinateShift.translation ε q =
      CoordinateShift.translation (ε + ε) a := by
    funext i
    simp [q, CoordinateShift.translation_apply, NNReal.coe_add, add_assoc]
  have hfinal : e ≤ CoordinateShift.translation (ε + ε) a := by
    rw [← hdouble]
    exact hmid
  let x : (HookInfinity.module (R := k) c).obj q :=
    (f.app a).hom (HookInfinity.birth a)
  let z : (HookInfinity.module (R := k) e).obj (CoordinateShift.translation ε q) :=
    (g.app q).hom x
  have hx : x = principalHookCoefficient (k := k) ε f •
      structureMapLinear (HookInfinity.module (R := k) c) hq
        (HookInfinity.birth c) := by
    have hcoeff : HookInfinity.fiberEquivOfLe (R := k) hq x =
        principalHookCoefficient (k := k) ε f := by
      simp [principalHookCoefficient, q, hq, x]
    rw [principalHook_birth_span hq x, hcoeff]
  have hnat := g.naturality (homOfLE hq)
  have hmul : HookInfinity.fiberEquivOfLe (R := k) hmid z =
        principalHookCoefficient (k := k) ε f *
          principalHookCoefficient (k := k) ε g := by
    change HookInfinity.fiberEquivOfLe (R := k) hmid
      ((g.app q).hom x) = _
    rw [hx, map_smul]
    have hnat' : (g.app q).hom
        (structureMapLinear (HookInfinity.module (R := k) c) hq
          (HookInfinity.birth c)) =
        structureMapLinear ((CoordinateShift.shift ε).obj
          (HookInfinity.module (R := k) e))
          hq
          ((g.app c).hom (HookInfinity.birth c)) := by
      have hn := congrArg (fun f => f.hom (HookInfinity.birth c)) hnat
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
        structureMapLinear, structureMap] using hn
    rw [hnat']
    have hshift : structureMapLinear ((CoordinateShift.shift ε).obj
        (HookInfinity.module (R := k) e)) hq =
        structureMapLinear (HookInfinity.module (R := k) e)
          ((CoordinateShift.translation ε).monotone' hq) := by
      rfl
    rw [hshift]
    have hcoeffG : HookInfinity.fiberEquivOfLe (R := k) hmid
        (structureMapLinear (HookInfinity.module (R := k) e)
          ((CoordinateShift.translation ε).monotone' hq)
          ((g.app c).hom (HookInfinity.birth c))) =
        principalHookCoefficient (k := k) ε g := by
      have hs := HookInfinity.fiberEquivOfLe_structureMap (R := k)
        (hia := hec) (hab := (CoordinateShift.translation ε).monotone' hq)
        ((g.app c).hom (HookInfinity.birth c))
      simpa [principalHookCoefficient, hec] using hs
    calc
      _ = principalHookCoefficient (k := k) ε f *
          HookInfinity.fiberEquivOfLe (R := k) hmid
            (structureMapLinear (HookInfinity.module (R := k) e)
              ((CoordinateShift.translation ε).monotone' hq)
              ((g.app c).hom (HookInfinity.birth c))) := by
        exact LinearEquiv.map_smul
          (HookInfinity.fiberEquivOfLe (R := k) hmid)
          (principalHookCoefficient (k := k) ε f)
          (structureMapLinear (HookInfinity.module (R := k) e)
            ((CoordinateShift.translation ε).monotone' hq)
            ((g.app c).hom (HookInfinity.birth c)))
      _ = principalHookCoefficient (k := k) ε f *
          principalHookCoefficient (k := k) ε g := by rw [hcoeffG]
  have hcompVal : HookInfinity.fiberEquivOfLe (R := k) hfinal
      (((f ≫ (CoordinateShift.shift ε).map g ≫
        (CoordinateShift.compIso ε ε (HookInfinity.module (R := k) e)).hom).app a).hom
          (HookInfinity.birth a)) =
        principalHookCoefficient (k := k) ε f *
          principalHookCoefficient (k := k) ε g := by
    change HookInfinity.fiberEquivOfLe (R := k) hfinal
      (((CoordinateShift.compIso ε ε (HookInfinity.module (R := k) e)).hom.app a).hom
        z) = _
    rw [CoordinateShift.compIso_hom_app]
    change HookInfinity.fiberEquivOfLe (R := k) hfinal
      (structureMapLinear (HookInfinity.module (R := k) e)
        (leOfHom (eqToHom hdouble)) z) = _
    rw [HookInfinity.fiberEquivOfLe_structureMap]
    exact hmul
  simpa [principalHookCoefficient, hfinal] using hcompVal

/-- The diagonal coefficient of a principal-upset transition is one: unlike a
finite-death hook, a principal upset survives every finite translation. -/
theorem principalHookCoefficient_transition {a : Fin n → ℝ} (δ : ℝ≥0) :
    principalHookCoefficient (k := k) δ
      (CoordinateShift.transition δ (HookInfinity.module (R := k) a)) = 1 := by
  classical
  have h : a ≤ CoordinateShift.translation δ a := by
    intro i
    change a i ≤ a i + (δ : ℝ)
    exact le_add_of_nonneg_right δ.coe_nonneg
  unfold principalHookCoefficient
  rw [dif_pos h]
  change HookInfinity.fiberEquivOfLe (R := k) h
    (structureMapLinear (HookInfinity.module (R := k) a) h
      (HookInfinity.birth a)) = 1
  rw [HookInfinity.fiberEquivOfLe_structureMap (R := k) (le_rfl : a ≤ a) h]
  change (HookInfinity.birth a).val () = 1
  simp [HookInfinity.birth, GradedFree.birth, GradedFree.generator]

/-- Coordinatewise birth closeness produces the actual two natural maps for
principal-upset hooks. The double-shift equations are checked on the birth
generators, using multiplicativity of the map coefficients. -/
noncomputable def principalHookInterleavingOfBirthClose {a c : Fin n → ℝ}
    (ρ : ℝ≥0)
    (hac : ∀ i, c i ≤ a i + (ρ : ℝ))
    (hca : ∀ i, a i ≤ c i + (ρ : ℝ)) :
    CoordinateInterleaving ρ (HookInfinity.module (R := k) a)
      (HookInfinity.module (R := k) c) := by
  let hAC : c ≤ CoordinateShift.translation ρ a := by
    intro i
    simpa [CoordinateShift.translation_apply] using hac i
  let hCA : a ≤ CoordinateShift.translation ρ c := by
    intro i
    simpa [CoordinateShift.translation_apply] using hca i
  let f : HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ρ).obj (HookInfinity.module (R := k) c) :=
    HookInfinity.fromBirth a ((CoordinateShift.shift ρ).obj
      (HookInfinity.module (R := k) c))
      (structureMapLinear (HookInfinity.module (R := k) c) hAC
        (HookInfinity.birth c))
  let g : HookInfinity.module (R := k) c ⟶
      (CoordinateShift.shift ρ).obj (HookInfinity.module (R := k) a) :=
    HookInfinity.fromBirth c ((CoordinateShift.shift ρ).obj
      (HookInfinity.module (R := k) a))
      (structureMapLinear (HookInfinity.module (R := k) a) hCA
        (HookInfinity.birth a))
  have hf : principalHookCoefficient (k := k) ρ f = 1 := by
    unfold principalHookCoefficient
    rw [dif_pos hAC]
    change HookInfinity.fiberEquivOfLe (R := k) hAC
      ((f.app a).hom (HookInfinity.birth a)) = 1
    rw [show (f.app a).hom (HookInfinity.birth a) =
      structureMapLinear (HookInfinity.module (R := k) c) hAC
        (HookInfinity.birth c) by
        exact HookInfinity.fromBirth_birth a _ _]
    rw [HookInfinity.fiberEquivOfLe_structureMap (R := k) (le_rfl : c ≤ c) hAC]
    change (HookInfinity.birth c).val () = 1
    simp [HookInfinity.birth, GradedFree.birth, GradedFree.generator]
  have hg : principalHookCoefficient (k := k) ρ g = 1 := by
    unfold principalHookCoefficient
    rw [dif_pos hCA]
    change HookInfinity.fiberEquivOfLe (R := k) hCA
      ((g.app c).hom (HookInfinity.birth c)) = 1
    rw [show (g.app c).hom (HookInfinity.birth c) =
      structureMapLinear (HookInfinity.module (R := k) a) hCA
        (HookInfinity.birth a) by
        exact HookInfinity.fromBirth_birth c _ _]
    rw [HookInfinity.fiberEquivOfLe_structureMap (R := k) (le_rfl : a ≤ a) hCA]
    change (HookInfinity.birth a).val () = 1
    simp [HookInfinity.birth, GradedFree.birth, GradedFree.generator]
  have hdoubleA : a ≤ CoordinateShift.translation (ρ + ρ) a := by
    intro i
    change a i ≤ a i + ((ρ + ρ : ℝ≥0) : ℝ)
    exact le_add_of_nonneg_right (by positivity)
  have hdoubleC : c ≤ CoordinateShift.translation (ρ + ρ) c := by
    intro i
    change c i ≤ c i + ((ρ + ρ : ℝ≥0) : ℝ)
    exact le_add_of_nonneg_right (by positivity)
  have hcompA : principalHookCoefficient (k := k) (ρ + ρ)
      (f ≫ (CoordinateShift.shift ρ).map g ≫
        (CoordinateShift.compIso ρ ρ (HookInfinity.module (R := k) a)).hom) = 1 := by
    rw [principalHookCoefficient_composite]
    simp [hf, hg]
  have hcompC : principalHookCoefficient (k := k) (ρ + ρ)
      (g ≫ (CoordinateShift.shift ρ).map f ≫
        (CoordinateShift.compIso ρ ρ (HookInfinity.module (R := k) c)).hom) = 1 := by
    rw [principalHookCoefficient_composite]
    simp [hf, hg, mul_comm]
  have hA : f ≫ (CoordinateShift.shift ρ).map g ≫
      (CoordinateShift.compIso ρ ρ (HookInfinity.module (R := k) a)).hom =
        CoordinateShift.transition (ρ + ρ) (HookInfinity.module (R := k) a) := by
    apply HookInfinity.hom_ext
    apply (HookInfinity.fiberEquivOfLe (R := k) hdoubleA).injective
    have hleft := hcompA
    have hright := principalHookCoefficient_transition (k := k) (a := a) (ρ + ρ)
    unfold principalHookCoefficient at hleft hright
    rw [dif_pos hdoubleA] at hleft hright
    exact hleft.trans hright.symm
  have hC : g ≫ (CoordinateShift.shift ρ).map f ≫
      (CoordinateShift.compIso ρ ρ (HookInfinity.module (R := k) c)).hom =
        CoordinateShift.transition (ρ + ρ) (HookInfinity.module (R := k) c) := by
    apply HookInfinity.hom_ext
    apply (HookInfinity.fiberEquivOfLe (R := k) hdoubleC).injective
    have hleft := hcompC
    have hright := principalHookCoefficient_transition (k := k) (a := c) (ρ + ρ)
    unfold principalHookCoefficient at hleft hright
    rw [dif_pos hdoubleC] at hleft hright
    exact hleft.trans hright.symm
  exact ⟨f, g, hA, hC⟩

private theorem hook_sum_reverse_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r s : ι → ℝ) (δ : ℝ)
    (hs : ∀ i, s i ≤ r i + δ)
    (ht : ∑ i, r i ≤ ∑ i, s i) (j : ι) :
    r j ≤ s j + ((Fintype.card ι : ℝ) - 1) * δ := by
  let t : Finset ι := Finset.univ.erase j
  have hrest : (∑ i ∈ t, (s i - r i)) ≤
      ((Fintype.card ι : ℝ) - 1) * δ := by
    have hcard : t.card = Fintype.card ι - 1 := by
      simp [t, Finset.card_erase_of_mem]
    calc
      (∑ i ∈ t, (s i - r i)) ≤ ∑ _i ∈ t, δ := by
        apply Finset.sum_le_sum
        intro i hi
        linarith [hs i]
      _ = ((Fintype.card ι : ℝ) - 1) * δ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hcard]
        have hc : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
        rw [Nat.cast_sub hc]
        norm_num
  have htotal : 0 ≤ ∑ i, (s i - r i) := by
    rw [Finset.sum_sub_distrib]
    exact sub_nonneg.mpr ht
  have hsplit : (∑ i, (s i - r i)) =
      (∑ i ∈ t, (s i - r i)) + (s j - r j) := by
    exact (Finset.sum_erase_add Finset.univ (fun i => s i - r i)
      (Finset.mem_univ j)).symm
  linarith

/-- Endpoint-sum order along two nonzero principal-upset maps forces their
first adjacent pair to be close at the finite-hook stability radius. -/
theorem principal_hook_path_birth_close (hn : 0 < n) (ε : ℝ≥0)
    {a c e : Fin n → ℝ}
    (hAE : (∑ i, a i) ≤ ∑ i, e i)
    (hAC : ∀ i, c i ≤ a i + (ε : ℝ))
    (hCE : ∀ i, e i ≤ c i + (ε : ℝ)) :
    ∀ i, c i ≤ a i +
        (RectangleStabilityGeometry.stabilityRadius n ε : ℝ) ∧
      a i ≤ c i + (RectangleStabilityGeometry.stabilityRadius n ε : ℝ) := by
  classical
  have hnat : 1 ≤ 2 * n := by omega
  have hrad : (RectangleStabilityGeometry.stabilityRadius n ε : ℝ) =
      ((2 * (n : ℝ) - 1) * (ε : ℝ)) := by
    simp only [RectangleStabilityGeometry.stabilityRadius, NNReal.coe_mul,
      NNReal.coe_natCast, Nat.cast_sub hnat]
    push_cast
    ring
  have hstep : ∀ i, e i ≤ a i + 2 * (ε : ℝ) := by
    intro i
    linarith [hAC i, hCE i]
  intro i
  have hrev := hook_sum_reverse_bound (r := a) (s := e)
    (2 * (ε : ℝ)) hstep hAE i
  constructor
  · rw [hrad]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hfactor : (1 : ℝ) ≤ 2 * (n : ℝ) - 1 := by linarith
    have hε := mul_le_mul_of_nonneg_right hfactor ε.coe_nonneg
    linarith [hAC i, hε]
  · rw [hrad]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hce := hCE i
    have hrev' : a i ≤ e i + ((n : ℝ) - 1) * (2 * (ε : ℝ)) := by
      simpa only [Fintype.card_fin] using hrev
    calc
      a i ≤ e i + ((n : ℝ) - 1) * (2 * (ε : ℝ)) := hrev'
      _ ≤ c i + (ε : ℝ) + ((n : ℝ) - 1) * (2 * (ε : ℝ)) := by
        linarith [hce]
      _ = c i + (2 * (n : ℝ) - 1) * (ε : ℝ) := by ring

/-- Nonzero maps between principal upsets force the one-sided birth bounds
used by the endpoint-sum path argument. -/
theorem nonzero_principalHook_map_birth_bound {a c : Fin n → ℝ}
    (ε : ℝ≥0)
    (f : HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c))
    (hf : f ≠ 0) :
    ∀ i, c i ≤ a i + (ε : ℝ) := by
  have hcoeff := (principalHookCoefficient_ne_zero_iff (k := k) ε f).2 hf
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have hnot : ¬ c ≤ CoordinateShift.translation ε a := by
    intro hle
    have := hle i
    change c i ≤ a i + (ε : ℝ) at this
    exact (not_le_of_gt hi) this
  exact hcoeff (by simp [principalHookCoefficient, hnot])

/-- The ordered two-step path through a principal hook contains an actual
interleaving edge at the matching radius. -/
theorem principal_hook_path_neighbor_of_maps (hn : 0 < n) (ε : ℝ≥0)
    {a c e : Fin n → ℝ}
    (hAE : (∑ i, a i) ≤ ∑ i, e i)
    (u : HookInfinity.module (R := k) a ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) (hu : u ≠ 0)
    (v : HookInfinity.module (R := k) c ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) e)) (hv : v ≠ 0) :
    Nonempty (CoordinateInterleaving
      (RectangleStabilityGeometry.stabilityRadius n ε)
      (HookInfinity.module (R := k) a) (HookInfinity.module (R := k) c)) := by
  have hAC := nonzero_principalHook_map_birth_bound (k := k) ε u hu
  have hCE := nonzero_principalHook_map_birth_bound (k := k) ε v hv
  have hclose := principal_hook_path_birth_close hn ε hAE hAC hCE
  exact ⟨principalHookInterleavingOfBirthClose (k := k)
    (RectangleStabilityGeometry.stabilityRadius n ε)
    (fun i => (hclose i).1) (fun i => (hclose i).2)⟩

/-- Every map from a finite-death hook to a shifted principal upset vanishes:
the source generator dies while every later target structure map is injective. -/
theorem finiteHook_to_principal_zero {a b c : Fin n → ℝ} (hab : a < b)
    (ε : ℝ≥0)
    (f : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (HookInfinity.module (R := k) c)) :
    f = 0 := by
  apply Hook.hom_ext hab
  let y := (f.app a).hom (SupportInterval.one (Hook.support a b)
    (Hook.birth_mem hab))
  change y = 0
  by_cases hca : c ≤ CoordinateShift.translation ε a
  · have hcb : c ≤ CoordinateShift.translation ε b :=
      hca.trans ((CoordinateShift.translation ε).monotone' hab.le)
    have hdie := Hook.generator_dies (k := k) hab f
    have hdie' : structureMapLinear (HookInfinity.module (R := k) c)
        ((CoordinateShift.translation ε).monotone' hab.le) y = 0 := by
      change structureMapLinear (HookInfinity.module (R := k) c)
        ((CoordinateShift.translation ε).monotone' hab.le) y = 0 at hdie
      exact hdie
    have hcoeff := congrArg (HookInfinity.fiberEquivOfLe (R := k) hcb) hdie'
    have hval : HookInfinity.fiberEquivOfLe (R := k) hca y = 0 := by
      calc
        HookInfinity.fiberEquivOfLe (R := k) hca y =
            HookInfinity.fiberEquivOfLe (R := k) hcb
              (structureMapLinear (HookInfinity.module (R := k) c)
                ((CoordinateShift.translation ε).monotone' hab.le) y) :=
          (HookInfinity.fiberEquivOfLe_structureMap (R := k) hca
            ((CoordinateShift.translation ε).monotone' hab.le) y).symm
        _ = 0 := hcoeff
    exact (HookInfinity.fiberEquivOfLe (R := k) hca).injective hval
  · exact HookInfinity.fiber_eq_zero_of_not_le (R := k) hca y

/-- A finite hook and a principal upset cannot interleave at any finite
parameter: the principal transition never vanishes, while the finite-to-
principal block is zero. -/
theorem not_interleaved_finite_principal {a b c : Fin n → ℝ}
    (hab : a < b) (ρ : ℝ≥0) :
    ¬ Nonempty (CoordinateInterleaving ρ (Hook.module (k := k) a b)
      (HookInfinity.module (R := k) c)) := by
  rintro ⟨I⟩
  have hφ := finiteHook_to_principal_zero hab ρ I.φ
  have hcomp : CoordinateShift.transition (ρ + ρ)
      (HookInfinity.module (R := k) c) = 0 := by
    simpa [hφ] using I.ψ_φ.symm
  have hcoeff := principalHookCoefficient_transition (k := k) (a := c) (ρ + ρ)
  rw [hcomp, principalHookCoefficient_zero] at hcoeff
  exact zero_ne_one hcoeff

/-- The reverse type order is also impossible by the other double-shift
equation and the same nonvanishing principal-upset transition. -/
theorem not_interleaved_principal_finite {a b c : Fin n → ℝ}
    (hab : a < b) (ρ : ℝ≥0) :
    ¬ Nonempty (CoordinateInterleaving ρ (HookInfinity.module (R := k) c)
      (Hook.module (k := k) a b)) := by
  rintro ⟨I⟩
  have hψ := finiteHook_to_principal_zero hab ρ I.ψ
  have hcomp : CoordinateShift.transition (ρ + ρ)
      (HookInfinity.module (R := k) c) = 0 := by
    simpa [hψ] using I.φ_ψ.symm
  have hcoeff := principalHookCoefficient_transition (k := k) (a := c) (ρ + ρ)
  rw [hcomp, principalHookCoefficient_zero] at hcoeff
  exact zero_ne_one hcoeff

/-- The target unit at a shifted source birth, or zero if the target support is
inactive there. -/
noncomputable def finiteHookMapBirthVector {a c d : Fin n → ℝ} (ε : ℝ≥0) :
    SupportInterval.fiber (k := k) (Hook.support c d)
      (CoordinateShift.translation ε a) :=
  if h : CoordinateShift.translation ε a ∈ Hook.support c d then
    SupportInterval.one (k := k) (Hook.support c d) h else 0

/-- A finite-hook morphism whose death bound guarantees its generator dies in
the target shift. -/
noncomputable def finiteHookMapOfDeathBound {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (hdb : ∀ i, d i ≤ b i + (ε : ℝ)) :
    Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d) := by
  let y := finiteHookMapBirthVector (k := k) (a := a) (c := c) (d := d) ε
  have hnot : CoordinateShift.translation ε b ∉ Hook.support c d := by
    intro h
    exact h.2 (fun i => by
      simpa only [CoordinateShift.translation_apply] using hdb i)
  have hdie : structureMapLinear ((CoordinateShift.shift ε).obj
      (Hook.module (k := k) c d)) hab.le y = 0 := by
    apply Subtype.ext
    change ((structureMapLinear
      (SupportInterval.module (k := k) (Hook.support c d)
        (Hook.support_ordConnected c d))
      ((CoordinateShift.translation ε).monotone' hab.le) y : k) = 0)
    rw [SupportInterval.structureMap_val,
      if_neg (show (CoordinateShift.translation ε).toFun b ∉ Hook.support c d from hnot)]
  exact Hook.fromGenerator hab ((CoordinateShift.shift ε).obj
    (Hook.module (k := k) c d)) y hdie

/-- The constructed map sends the source birth unit to its prescribed target
birth vector. -/
@[simp] theorem finiteHookMapOfDeathBound_birth {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0) (hdb : ∀ i, d i ≤ b i + (ε : ℝ)) :
    ((finiteHookMapOfDeathBound (k := k) hab ε hdb).app a).hom
      (SupportInterval.one (Hook.support a b) (Hook.birth_mem hab)) =
      finiteHookMapBirthVector (k := k) (a := a) (c := c) (d := d) ε := by
  unfold finiteHookMapOfDeathBound
  exact Hook.fromGenerator_birth hab _ _ _

/-- At every supported source grade, the constructed comparison map is the
target structure map applied to its birth vector. -/
theorem finiteHookMapOfDeathBound_app {a b c d p : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0) (hdb : ∀ i, d i ≤ b i + (ε : ℝ))
    (hap : a ≤ p) (x : SupportInterval.fiber (k := k) (Hook.support a b) p) :
    ((finiteHookMapOfDeathBound (k := k) hab ε hdb).app p).hom x =
      (x : k) • structureMapLinear (Hook.module (k := k) c d)
        ((CoordinateShift.translation ε).monotone' hap)
        (finiteHookMapBirthVector (k := k) (a := a) (c := c) (d := d) ε) := by
  unfold finiteHookMapOfDeathBound
  exact Hook.fromGenerator_app hab _ _ _ hap x

private theorem shiftedHook_app_val_eq_mul {S T : Set (Fin n → ℝ)}
    (hS : S.OrdConnected) (hT : T.OrdConnected) (ε : ℝ≥0)
    (u : SupportInterval.module (k := k) S hS ⟶
      (CoordinateShift.shift ε).obj (SupportInterval.module (k := k) T hT))
    {p : Fin n → ℝ} (hp : p ∈ S) (x : SupportInterval.fiber (k := k) S p) :
    ((show SupportInterval.fiber (k := k) T (CoordinateShift.translation ε p) from
      (u.app p).hom x) : k) = (x : k) *
      ((show SupportInterval.fiber (k := k) T (CoordinateShift.translation ε p) from
        (u.app p).hom (SupportInterval.one (k := k) S hp)) : k) := by
  have hx : x = (x : k) • SupportInterval.one (k := k) S hp := by
    apply Subtype.ext
    simp [SupportInterval.one]
  conv_lhs => rw [hx, map_smul]
  rfl

/-- On a common active grade, the coefficient of a composite of two shifted
finite-hook maps is the product of their coefficients. -/
theorem finiteHookCoefficient_composite_at {a b c d e f p : Fin n → ℝ}
    (hab : a < b) (hcd : c < d) (ε : ℝ≥0)
    (u : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d))
    (v : Hook.module (k := k) c d ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) e f))
    (hap : a ≤ p) (hpA : p ∈ Hook.support a b)
    (hpB : CoordinateShift.translation ε p ∈ Hook.support c d)
    (hpC : CoordinateShift.translation (ε + ε) p ∈ Hook.support e f) :
    finiteHookCoefficient (k := k) hab (ε + ε)
      (u ≫ (CoordinateShift.shift ε).map v ≫
        (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom) =
      finiteHookCoefficient (k := k) hab ε u *
        finiteHookCoefficient (k := k) hcd ε v := by
  classical
  let q := CoordinateShift.translation ε p
  let x := SupportInterval.one (k := k) (Hook.support a b) hpA
  let y : SupportInterval.fiber (k := k) (Hook.support c d) q := (u.app p).hom x
  let z : SupportInterval.fiber (k := k) (Hook.support e f)
      (CoordinateShift.translation ε q) := (v.app q).hom y
  have hdouble : CoordinateShift.translation ε q =
      CoordinateShift.translation (ε + ε) p := by
    funext i
    simp [q, CoordinateShift.translation_apply, NNReal.coe_add, add_assoc]
  have hEq : CoordinateShift.translation ε (CoordinateShift.translation ε p) =
      CoordinateShift.translation (ε + ε) p := by
    funext i
    change p i + (ε : ℝ) + (ε : ℝ) = p i + ((ε + ε : ℝ≥0) : ℝ)
    rw [NNReal.coe_add]
    ring
  have hpC' : CoordinateShift.translation ε q ∈ Hook.support e f := hdouble.symm ▸ hpC
  have hleft := finiteHookCoefficient_eq_at (k := k) hab (ε + ε)
    (u ≫ (CoordinateShift.shift ε).map v ≫
      (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom)
    hap hpA hpC
  have huCoeff := finiteHookCoefficient_eq_at (k := k) hab ε u hap hpA hpB
  have hvCoeff := finiteHookCoefficient_eq_at (k := k) hcd ε v hpB.1 hpB hpC'
  have htransport :
      ((show SupportInterval.fiber (k := k) (Hook.support e f)
          (CoordinateShift.translation (ε + ε) p) from
        ((CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom.app p).hom z) : k) =
        (z : k) := by
    rw [CoordinateShift.compIso_hom_app]
    change ((structureMapLinear
      (SupportInterval.module (k := k) (Hook.support e f)
        (Hook.support_ordConnected e f))
      (leOfHom (eqToHom hEq))
      z : k) = (z : k))
    rw [SupportInterval.structureMap_val, if_pos hpC]
  have hmul := shiftedHook_app_val_eq_mul (k := k)
    (Hook.support_ordConnected c d) (Hook.support_ordConnected e f) ε v hpB y
  have huCoeffY : finiteHookCoefficient (k := k) hab ε u = (y : k) := by
    simpa [y, x] using huCoeff
  have hvCoeffQ : finiteHookCoefficient (k := k) hcd ε v =
      ((show SupportInterval.fiber (k := k) (Hook.support e f)
        (CoordinateShift.translation ε q) from
        (v.app q).hom (SupportInterval.one (Hook.support c d) hpB)) : k) := by
    simpa [q] using hvCoeff
  calc
    finiteHookCoefficient (k := k) hab (ε + ε)
        (u ≫ (CoordinateShift.shift ε).map v ≫
          (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom) =
        ((show SupportInterval.fiber (k := k) (Hook.support e f)
          (CoordinateShift.translation (ε + ε) p) from
          ((u ≫ (CoordinateShift.shift ε).map v ≫
            (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom).app p).hom x) : k) := hleft
    _ = (z : k) := by
      simp only [NatTrans.comp_app, Category.assoc, CoordinateShift.shift_map_app]
      exact htransport
    _ = finiteHookCoefficient (k := k) hab ε u *
        finiteHookCoefficient (k := k) hcd ε v := by
      calc
        (z : k) = (y : k) *
            ((show SupportInterval.fiber (k := k) (Hook.support e f)
              (CoordinateShift.translation ε q) from
              (v.app q).hom (SupportInterval.one (Hook.support c d) hpB)) : k) := hmul
        _ = finiteHookCoefficient (k := k) hab ε u *
            finiteHookCoefficient (k := k) hcd ε v := by
          rw [← huCoeffY, ← hvCoeffQ]

private theorem finiteHook_pair_composite {a b c d : Fin n → ℝ}
    (hab : a < b) (hcd : c < d) (ρ : ℝ≥0)
    (hca : ∀ i, c i ≤ a i + (ρ : ℝ))
    (hdb : ∀ i, d i ≤ b i + (ρ : ℝ))
    (hac : ∀ i, a i ≤ c i + (ρ : ℝ))
    (hbd : ∀ i, b i ≤ d i + (ρ : ℝ)) :
    let forward := finiteHookMapOfDeathBound (k := k) (a := a) (b := b)
      (c := c) (d := d) hab ρ hdb
    let reverse := finiteHookMapOfDeathBound (k := k) (a := c) (b := d)
      (c := a) (d := b) hcd ρ hbd
    forward ≫ (shift ρ).map reverse ≫
      (compIso ρ ρ (Hook.module (k := k) a b)).hom =
        transition (ρ + ρ) (Hook.module (k := k) a b) := by
  dsimp only
  let forward := finiteHookMapOfDeathBound (k := k) (a := a) (b := b)
    (c := c) (d := d) hab ρ hdb
  let reverse := finiteHookMapOfDeathBound (k := k) (a := c) (b := d)
    (c := a) (d := b) hcd ρ hbd
  apply Hook.hom_ext hab
  let q := CoordinateShift.translation ρ a
  let q₂ := CoordinateShift.translation ρ q
  have hq₂ : q₂ = CoordinateShift.translation (ρ + ρ) a := by
    funext i
    dsimp [q₂, q, CoordinateShift.translation]
    change (a i + (ρ : ℝ)) + (ρ : ℝ) =
      a i + ((ρ + ρ : ℝ≥0) : ℝ)
    rw [NNReal.coe_add]
    ring
  by_cases hA₂ : q₂ ∈ Hook.support a b
  · have hqB : q ∈ Hook.support c d := by
      refine ⟨?_, ?_⟩
      · intro i
        change c i ≤ a i + (ρ : ℝ)
        exact hca i
      · intro hdbq
        apply hA₂.2
        intro i
        have hbdi := hbd i
        change b i ≤ d i + (ρ : ℝ) at hbdi
        have hq : d i ≤ a i + (ρ : ℝ) := hdbq i
        change b i ≤ (a i + (ρ : ℝ)) + (ρ : ℝ)
        have hq' : d i + (ρ : ℝ) ≤ (a i + (ρ : ℝ)) + (ρ : ℝ) := by
          linarith
        exact hbdi.trans hq'
    have hcρ : CoordinateShift.translation ρ c ∈ Hook.support a b := by
      apply (Hook.support_ordConnected a b).out (Hook.birth_mem hab) hA₂
      constructor
      · intro i
        change a i ≤ c i + (ρ : ℝ)
        exact hac i
      · intro i
        change c i + (ρ : ℝ) ≤ (a i + (ρ : ℝ)) + (ρ : ℝ)
        linarith [hca i]
    have hcomp := finiteHookCoefficient_composite_at (k := k) hab hcd ρ
      forward reverse (le_rfl : a ≤ a) (Hook.birth_mem hab) hqB (hq₂ ▸ hA₂)
    have hfwd : finiteHookCoefficient (k := k) hab ρ forward = 1 := by
      change ((show SupportInterval.fiber (k := k) (Hook.support c d)
        (CoordinateShift.translation ρ a) from
        (forward.app a).hom (SupportInterval.one (Hook.support a b)
          (Hook.birth_mem hab)) : k)) = 1
      rw [finiteHookMapOfDeathBound_birth, finiteHookMapBirthVector, dif_pos hqB]
      rfl
    have hrev : finiteHookCoefficient (k := k) hcd ρ reverse = 1 := by
      change ((show SupportInterval.fiber (k := k) (Hook.support a b)
        (CoordinateShift.translation ρ c) from
        (reverse.app c).hom (SupportInterval.one (Hook.support c d)
          (Hook.birth_mem hcd)) : k)) = 1
      rw [finiteHookMapOfDeathBound_birth, finiteHookMapBirthVector, dif_pos hcρ]
      rfl
    have hcomp' : finiteHookCoefficient (k := k) hab (ρ + ρ)
        (forward ≫ (shift ρ).map reverse ≫
          (compIso ρ ρ (Hook.module (k := k) a b)).hom) = 1 := by
      simpa [hfwd, hrev] using hcomp
    have htrans : finiteHookCoefficient (k := k) hab (ρ + ρ)
        (transition (ρ + ρ) (Hook.module (k := k) a b)) = 1 := by
      rw [finiteHookCoefficient_eq_at (k := k) hab (ρ + ρ)
        (transition (ρ + ρ) (Hook.module (k := k) a b)) le_rfl
        (Hook.birth_mem hab) (hq₂ ▸ hA₂)]
      simp only [CoordinateShift.transition_app]
      change ((structureMapLinear (Hook.module (k := k) a b)
        (show a ≤ CoordinateShift.translation (ρ + ρ) a from fun i => by
          change a i ≤ a i + ((ρ + ρ : ℝ≥0) : ℝ)
          exact le_add_of_nonneg_right (show 0 ≤ ((ρ + ρ : ℝ≥0) : ℝ) from
            NNReal.coe_nonneg (ρ + ρ)))
        (SupportInterval.one (Hook.support a b) (Hook.birth_mem hab)) : k) = 1)
      rw [SupportInterval.structureMap_val, if_pos (hq₂ ▸ hA₂)]
      rfl
    apply Subtype.ext
    change finiteHookCoefficient (k := k) hab (ρ + ρ)
        (forward ≫ (shift ρ).map reverse ≫
          (compIso ρ ρ (Hook.module (k := k) a b)).hom) =
      finiteHookCoefficient (k := k) hab (ρ + ρ)
        (transition (ρ + ρ) (Hook.module (k := k) a b))
    rw [hcomp', htrans]
  · apply Subtype.ext
    have hnot : CoordinateShift.translation (ρ + ρ) a ∉ Hook.support a b := by
      simpa [hq₂] using hA₂
    have hleft := SupportInterval.val_eq_zero (Hook.support a b) hnot
      (show SupportInterval.fiber (k := k) (Hook.support a b)
        (CoordinateShift.translation (ρ + ρ) a) from
        ((forward ≫ (shift ρ).map reverse ≫
          (compIso ρ ρ (Hook.module (k := k) a b)).hom).app a).hom
          (SupportInterval.one (Hook.support a b) (Hook.birth_mem hab)))
    have hright := SupportInterval.val_eq_zero (Hook.support a b) hnot
      (show SupportInterval.fiber (k := k) (Hook.support a b)
        (CoordinateShift.translation (ρ + ρ) a) from
        ((transition (ρ + ρ) (Hook.module (k := k) a b)).app a).hom
          (SupportInterval.one (Hook.support a b) (Hook.birth_mem hab)))
    exact hleft.trans hright.symm

/-- The endpoint inequalities for two finite-death hooks construct an actual
interleaving: the forward and reverse maps are the generator maps whose death
bounds are exactly the corresponding inequalities. -/
theorem finiteHook_endpoint_close_interleaving {a b c d : Fin n → ℝ}
    (hab : a < b) (hcd : c < d) (ρ : ℝ≥0)
    (hca : ∀ i, c i ≤ a i + (ρ : ℝ))
    (hdb : ∀ i, d i ≤ b i + (ρ : ℝ))
    (hac : ∀ i, a i ≤ c i + (ρ : ℝ))
    (hbd : ∀ i, b i ≤ d i + (ρ : ℝ)) :
    Nonempty (CoordinateInterleaving ρ
      (Hook.module (k := k) a b) (Hook.module (k := k) c d)) := by
  let forward := finiteHookMapOfDeathBound (k := k) (a := a) (b := b)
    (c := c) (d := d) hab ρ hdb
  let reverse := finiteHookMapOfDeathBound (k := k) (a := c) (b := d)
    (c := a) (d := b) hcd ρ hbd
  have hforward := finiteHook_pair_composite (k := k) hab hcd ρ hca hdb hac hbd
  have hreverse := finiteHook_pair_composite (k := k) hcd hab ρ hac hbd hca hdb
  exact ⟨⟨forward, reverse, by simpa [forward, reverse] using hforward,
    by simpa [forward, reverse] using hreverse⟩⟩


/-- Endpoint-sum order upgrades the one-sided bounds of a nonzero map to
two-sided endpoint closeness at radius `(2n - 1) ε`. -/
theorem finite_endpoint_reverse_bounds (hn : 0 < n) (ε : ℝ≥0)
    {a b c d : Fin n → ℝ} (hα :
      (∑ i, a i) + (∑ i, b i) ≤ (∑ i, c i) + (∑ i, d i))
    (hca : ∀ i, c i ≤ a i + (ε : ℝ))
    (hdb : ∀ i, d i ≤ b i + (ε : ℝ)) :
    (∀ i, a i ≤ c i + (2 * (n : ℝ) - 1) * (ε : ℝ)) ∧
      (∀ i, b i ≤ d i + (2 * (n : ℝ) - 1) * (ε : ℝ)) := by
  constructor
  · intro i
    by_contra hbad
    have hbad : c i + (2 * (n : ℝ) - 1) * (ε : ℝ) < a i := lt_of_not_ge hbad
    let E := Finset.univ.erase i
    have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    have hsumC : (∑ j, c j) = c i + ∑ j ∈ E, c j := by
      simpa [E] using Finset.add_sum_erase (Finset.univ : Finset (Fin n)) c hi
    have hrest : (∑ j ∈ E, c j) ≤ (∑ j ∈ E, a j) + (n - 1 : ℝ) * (ε : ℝ) := by
      calc
        (∑ j ∈ E, c j) ≤ ∑ j ∈ E, (a j + (ε : ℝ)) :=
          Finset.sum_le_sum fun j hj => hca j
        _ = (∑ j ∈ E, a j) + (E.card : ℝ) * (ε : ℝ) := by
          simp [Finset.sum_add_distrib, E, nsmul_eq_mul]
        _ = (∑ j ∈ E, a j) + (n - 1 : ℝ) * (ε : ℝ) := by
          have hcard : E.card = n - 1 := by simp [E, hi]
          rw [hcard, Nat.cast_sub (by omega : 1 ≤ n)]
          ring
    have hsumD : (∑ j, d j) ≤ (∑ j, b j) + (n : ℝ) * (ε : ℝ) := by
      calc
        (∑ j, d j) ≤ ∑ j, (b j + (ε : ℝ)) := Finset.sum_le_sum fun j hj => hdb j
        _ = (∑ j, b j) + (n : ℝ) * (ε : ℝ) := by
          simp [Finset.sum_add_distrib, nsmul_eq_mul]
    have hsumAB : (∑ j, a j) = a i + ∑ j ∈ E, a j := by
      simpa [E] using Finset.add_sum_erase (Finset.univ : Finset (Fin n)) a hi
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
    have hcontr : (∑ j, c j) + (∑ j, d j) < (∑ j, a j) + (∑ j, b j) := by
      rw [hsumC, hsumAB]
      linarith
    exact (not_lt_of_ge hα) hcontr
  · intro i
    by_contra hbad
    have hbad : d i + (2 * (n : ℝ) - 1) * (ε : ℝ) < b i := lt_of_not_ge hbad
    let E := Finset.univ.erase i
    have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    have hsumD : (∑ j, d j) = d i + ∑ j ∈ E, d j := by
      simpa [E] using Finset.add_sum_erase (Finset.univ : Finset (Fin n)) d hi
    have hrest : (∑ j ∈ E, d j) ≤ (∑ j ∈ E, b j) + (n - 1 : ℝ) * (ε : ℝ) := by
      calc
        (∑ j ∈ E, d j) ≤ ∑ j ∈ E, (b j + (ε : ℝ)) :=
          Finset.sum_le_sum fun j hj => hdb j
        _ = (∑ j ∈ E, b j) + (E.card : ℝ) * (ε : ℝ) := by
          simp [Finset.sum_add_distrib, E, nsmul_eq_mul]
        _ = (∑ j ∈ E, b j) + (n - 1 : ℝ) * (ε : ℝ) := by
          have hcard : E.card = n - 1 := by simp [E, hi]
          rw [hcard, Nat.cast_sub (by omega : 1 ≤ n)]
          ring
    have hsumC : (∑ j, c j) ≤ (∑ j, a j) + (n : ℝ) * (ε : ℝ) := by
      calc
        (∑ j, c j) ≤ ∑ j, (a j + (ε : ℝ)) := Finset.sum_le_sum fun j hj => hca j
        _ = (∑ j, a j) + (n : ℝ) * (ε : ℝ) := by
          simp [Finset.sum_add_distrib, nsmul_eq_mul]
    have hsumAB : (∑ j, b j) = b i + ∑ j ∈ E, b j := by
      simpa [E] using Finset.add_sum_erase (Finset.univ : Finset (Fin n)) b hi
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
    have hcontr : (∑ j, c j) + (∑ j, d j) < (∑ j, a j) + (∑ j, b j) := by
      rw [hsumD, hsumAB]
      linarith
    exact (not_lt_of_ge hα) hcontr

/-- Coordinatewise two-sided endpoint closeness for finite hooks. -/
def FiniteEndpointClose (ρ : ℝ) (a b c d : Fin n → ℝ) : Prop :=
  ∀ i, c i ≤ a i + ρ ∧ a i ≤ c i + ρ ∧ d i ≤ b i + ρ ∧ b i ≤ d i + ρ

/-- The finite-hook path lemma behind Theorem 4.1(1): endpoint-sum order and
two actual nonzero shifted maps force one adjacent pair to be close at the
constant `(2n - 1) ε`. -/
theorem finite_hook_path_endpoint_close (hn : 0 < n) (ε : ℝ≥0)
    {a b c d e f : Fin n → ℝ}
    (hRT : (∑ i, a i) + (∑ i, b i) ≤ (∑ i, e i) + (∑ i, f i))
    (hRS₁ : ∀ i, c i ≤ a i + (ε : ℝ))
    (hRS₂ : ∀ i, d i ≤ b i + (ε : ℝ))
    (hST₁ : ∀ i, e i ≤ c i + (ε : ℝ))
    (hST₂ : ∀ i, f i ≤ d i + (ε : ℝ)) :
    FiniteEndpointClose ((2 * (n : ℝ) - 1) * (ε : ℝ)) a b c d ∨
      FiniteEndpointClose ((2 * (n : ℝ) - 1) * (ε : ℝ)) c d e f := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hε : (ε : ℝ) ≤ (2 * (n : ℝ) - 1) * (ε : ℝ) := by
    have hc : (1 : ℝ) ≤ 2 * (n : ℝ) - 1 := by linarith
    calc
      (ε : ℝ) = 1 * (ε : ℝ) := by ring
      _ ≤ (2 * (n : ℝ) - 1) * (ε : ℝ) :=
        mul_le_mul_of_nonneg_right hc ε.coe_nonneg
  by_cases hRS : (∑ i, a i) + (∑ i, b i) ≤ (∑ i, c i) + (∑ i, d i)
  · left
    obtain ⟨ha, hb⟩ := finite_endpoint_reverse_bounds hn ε hRS hRS₁ hRS₂
    intro i
    exact ⟨(hRS₁ i).trans (add_le_add_right hε _), ha i,
      (hRS₂ i).trans (add_le_add_right hε _), hb i⟩
  · right
    have hST : (∑ i, c i) + (∑ i, d i) ≤ (∑ i, e i) + (∑ i, f i) :=
      le_trans (le_of_lt (lt_of_not_ge hRS)) hRT
    obtain ⟨hc, hd⟩ := finite_endpoint_reverse_bounds hn ε hST hST₁ hST₂
    intro i
    exact ⟨(hST₁ i).trans (add_le_add_right hε _), hc i,
      (hST₂ i).trans (add_le_add_right hε _), hd i⟩

/-- Actual nonzero maps of finite hooks supply the endpoint inequalities in the
ordered-path lemma, so its conclusion applies to interleaving components
without assuming their endpoint bounds separately. -/
theorem finite_hook_path_endpoint_close_of_maps (hn : 0 < n) (ε : ℝ≥0)
    {a b c d e f : Fin n → ℝ}
    (hRT : (∑ i, a i) + (∑ i, b i) ≤ (∑ i, e i) + (∑ i, f i))
    (hab : a < b)
    (u : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) (hu : u ≠ 0)
    (hcd : c < d)
    (v : Hook.module (k := k) c d ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) e f)) (hv : v ≠ 0) :
    FiniteEndpointClose ((2 * (n : ℝ) - 1) * (ε : ℝ)) a b c d ∨
      FiniteEndpointClose ((2 * (n : ℝ) - 1) * (ε : ℝ)) c d e f := by
  have hU := nonzero_finiteHook_map_endpoint_bounds hab ε u hu
  have hV := nonzero_finiteHook_map_endpoint_bounds hcd ε v hv
  exact finite_hook_path_endpoint_close hn ε hRT hU.1 hU.2 hV.1 hV.2

/-- Along an ordered path of two nonzero finite-hook maps, one of its two
edges is an actual interleaving at the stability radius. Endpoint closeness
is converted to concrete generator maps; the conclusion is not a hom
nonvanishing surrogate. -/
theorem finite_hook_path_neighbor_of_maps (hn : 0 < n) (ε : ℝ≥0)
    {a b c d e f : Fin n → ℝ}
    (hRT : (∑ i, a i) + (∑ i, b i) ≤ (∑ i, e i) + (∑ i, f i))
    (hab : a < b)
    (u : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) (hu : u ≠ 0)
    (hcd : c < d) (hef : e < f)
    (v : Hook.module (k := k) c d ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) e f)) (hv : v ≠ 0) :
    Nonempty (CoordinateInterleaving (RectangleStabilityGeometry.stabilityRadius n ε)
      (Hook.module (k := k) a b) (Hook.module (k := k) c d)) ∨
    Nonempty (CoordinateInterleaving (RectangleStabilityGeometry.stabilityRadius n ε)
      (Hook.module (k := k) c d) (Hook.module (k := k) e f)) := by
  have hnat : 1 ≤ 2 * n := by omega
  have hrad : (RectangleStabilityGeometry.stabilityRadius n ε : ℝ) =
      ((2 * (n : ℝ) - 1) * (ε : ℝ)) := by
    simp only [RectangleStabilityGeometry.stabilityRadius, NNReal.coe_mul,
      NNReal.coe_natCast, Nat.cast_sub hnat]
    push_cast
    ring
  rcases finite_hook_path_endpoint_close_of_maps (k := k) hn ε hRT hab u hu hcd v hv
    with h | h
  · left
    apply finiteHook_endpoint_close_interleaving hab hcd
      (RectangleStabilityGeometry.stabilityRadius n ε)
    · intro i
      simpa [hrad] using (h i).1
    · intro i
      simpa [hrad] using (h i).2.2.1
    · intro i
      simpa [hrad] using (h i).2.1
    · intro i
      simpa [hrad] using (h i).2.2.2
  · right
    apply finiteHook_endpoint_close_interleaving hcd hef
      (RectangleStabilityGeometry.stabilityRadius n ε)
    · intro i
      simpa [hrad] using (h i).1
    · intro i
      simpa [hrad] using (h i).2.2.1
    · intro i
      simpa [hrad] using (h i).2.1
    · intro i
      simpa [hrad] using (h i).2.2.2

/-- A finite-death hook is significant at radius `δ` exactly when at least
one coordinate remains strictly before its death after translation by `δ`.
The strict inequality is the correct convention at the endpoint. -/
def finiteSignificant (δ : ℝ≥0) (ab : FiniteHookTag (n := n)) : Prop :=
  ∃ i : Fin n, ab.val.2 i > ab.val.1 i + (δ : ℝ)

/-- The significance predicate used on finite or principal hook occurrences.
Every principal upset survives every finite shift. -/
def tagSignificant (δ : ℝ≥0) : RealHookTag (n := n) → Prop
  | .inl ab => finiteSignificant δ ab
  | .inr _ => True

/-- The support of a finite-death hook meets its `δ`-translate precisely when
one coordinate gap is strictly greater than `δ`. -/
theorem finiteHook_support_transition_iff (δ : ℝ≥0)
    (ab : FiniteHookTag (n := n)) :
    (∃ p : Fin n → ℝ, p ∈ Hook.support ab.val.1 ab.val.2 ∧
      CoordinateShift.translation δ p ∈ Hook.support ab.val.1 ab.val.2) ↔
        finiteSignificant δ ab := by
  constructor
  · rintro ⟨p, hp, hp'⟩
    have hnot : ¬ ∀ i : Fin n, ab.val.2 i ≤ p i + (δ : ℝ) := by
      intro h
      exact hp'.2 (fun i => h i)
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    refine ⟨i, ?_⟩
    have ha : ab.val.1 i ≤ p i := hp.1 i
    linarith [hi, ha]
  · rintro ⟨i, hi⟩
    refine ⟨ab.val.1, Hook.birth_mem ab.property, ?_⟩
    refine ⟨fun j => ?_, ?_⟩
    · change ab.val.1 j ≤ ab.val.1 j + (δ : ℝ)
      exact le_add_of_nonneg_right δ.coe_nonneg
    · intro h
      exact (not_le_of_gt hi) (h i)

/-- A support interval has a nonzero transition exactly when some point and
its translate both belong to its support. -/
theorem transition_ne_zero_iff_support {S : Set (Fin n → ℝ)}
    (hS : S.OrdConnected) (δ : ℝ≥0) :
    CoordinateShift.transition δ (SupportInterval.module (k := k) S hS) ≠ 0 ↔
      ∃ p, p ∈ S ∧ CoordinateShift.translation δ p ∈ S := by
  classical
  constructor
  · intro htrans
    by_contra h
    apply htrans
    apply NatTrans.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change structureMapLinear (SupportInterval.module (k := k) S hS)
      (show p ≤ CoordinateShift.translation δ p from fun i => by
        change p i ≤ p i + (δ : ℝ)
        exact le_add_of_nonneg_right δ.coe_nonneg) x = 0
    have hpnot : ¬ (p ∈ S ∧ CoordinateShift.translation δ p ∈ S) := by
      intro hp
      exact h ⟨p, hp.1, hp.2⟩
    exact congrArg (fun f => f x)
      (SupportInterval.structureMap_eq_zero_of_not_mem S hS _ hpnot)
  · rintro ⟨p, hp, hp'⟩ hzero
    have he := congrArg
      (fun f : SupportInterval.module (k := k) S hS ⟶
        (CoordinateShift.shift δ).obj (SupportInterval.module (k := k) S hS) =>
        (f.app p).hom (SupportInterval.one (k := k) S hp)) hzero
    have hv := congrArg Subtype.val he
    have hpδ : p ≤ CoordinateShift.translation δ p := fun i => by
      change p i ≤ p i + (δ : ℝ)
      exact le_add_of_nonneg_right δ.coe_nonneg
    change ((structureMapLinear (SupportInterval.module (k := k) S hS)
      hpδ (SupportInterval.one (k := k) S hp) : k) = 0) at hv
    rw [SupportInterval.structureMap_val] at hv
    simp only [hp', SupportInterval.one] at hv
    exact one_ne_zero hv

/-- A finite-death hook survives its `δ`-transition exactly at the strict
coordinate-gap threshold. -/
theorem finiteSignificant_iff_transition_ne_zero (δ : ℝ≥0)
    (ab : FiniteHookTag (n := n)) :
    finiteSignificant δ ab ↔
      CoordinateShift.transition δ
        (Hook.module (k := k) ab.val.1 ab.val.2) ≠ 0 := by
  rw [transition_ne_zero_iff_support (k := k)
    (Hook.support_ordConnected ab.val.1 ab.val.2) δ]
  exact (finiteHook_support_transition_iff δ ab).symm

private theorem sum_lt_sum_add_const_sub {m : ℕ} (x y : Fin m → ℝ)
    (i : Fin m) (C H : ℝ) (hweak : ∀ j, x j ≤ y j + C)
    (hstrict : x i < y i + C - H) :
    (∑ j, x j) < (∑ j, y j) + (m : ℝ) * C - H := by
  classical
  let E := (Finset.univ : Finset (Fin m)).erase i
  have hi : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i
  have hcard : (E.card : ℝ) = (m : ℝ) - 1 := by
    have hcardNat : E.card = m - 1 := by simp [E, hi]
    have hm : 0 < m := Fin.pos i
    rw [hcardNat, Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hxSplit : (∑ j, x j) = x i + ∑ j ∈ E, x j := by
    simpa [E] using Finset.add_sum_erase (Finset.univ : Finset (Fin m)) x hi
  have hySplit : (∑ j, y j) = y i + ∑ j ∈ E, y j := by
    simpa [E] using Finset.add_sum_erase (Finset.univ : Finset (Fin m)) y hi
  have hrest : (∑ j ∈ E, x j) ≤ (∑ j ∈ E, y j) + (E.card : ℝ) * C := by
    calc
      (∑ j ∈ E, x j) ≤ ∑ j ∈ E, (y j + C) :=
        Finset.sum_le_sum fun j hj => hweak j
      _ = (∑ j ∈ E, y j) + (E.card : ℝ) * C := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
  calc
    (∑ j, x j) = x i + ∑ j ∈ E, x j := hxSplit
    _ < (y i + C - H) + ((∑ j ∈ E, y j) + (E.card : ℝ) * C) :=
      add_lt_add_of_lt_of_le hstrict hrest
    _ = (∑ j, y j) + (m : ℝ) * C - H := by rw [hySplit, hcard]; ring

/-- The endpoint bounds from two nonzero maps force the second translate of
the first birth into the final hook whenever the two end hooks are significant
and ordered by the sum of their endpoints. -/
theorem finiteHook_composite_birth_target_of_significant (hn : 0 < n)
    (ε : ℝ≥0) {a b c d e f : Fin n → ℝ}
    (hab : a < b) (hcd : c < d) (hef : e < f)
    (hα : (∑ i, a i) + (∑ i, b i) ≤ (∑ i, e i) + (∑ i, f i))
    (hR : finiteSignificant (RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε) ⟨(a, b), hab⟩)
    (hT : finiteSignificant (RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε) ⟨(e, f), hef⟩)
    (u : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) (hu : u ≠ 0)
    (v : Hook.module (k := k) c d ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) e f)) (hv : v ≠ 0) :
    CoordinateShift.translation (ε + ε) a ∈ Hook.support e f := by
  classical
  have hnat : 1 ≤ 2 * n := by omega
  have hρ : (RectangleStabilityGeometry.stabilityRadius n ε : ℝ) =
      ((2 * (n : ℝ) - 1) * (ε : ℝ)) := by
    simp only [RectangleStabilityGeometry.stabilityRadius, NNReal.coe_mul,
      NNReal.coe_natCast, Nat.cast_sub hnat]
    push_cast
    ring
  have h2ρ : ((RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε : ℝ≥0) : ℝ) =
      2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
    simp [NNReal.coe_add]
    ring
  obtain ⟨i, hi⟩ := hR
  obtain ⟨j, hj⟩ := hT
  have hi' : b i > a i + 2 *
      ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
    simpa [h2ρ] using hi
  have hj' : f j > e j + 2 *
      ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
    simpa [h2ρ] using hj
  have hU := nonzero_finiteHook_map_endpoint_bounds hab ε u hu
  have hV := nonzero_finiteHook_map_endpoint_bounds hcd ε v hv
  have heBirth : ∀ l, e l ≤ a l + 2 * (ε : ℝ) := by
    intro l
    have h1 : c l ≤ a l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hU.1 l
    have h2 : e l ≤ c l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hV.1 l
    linarith
  have hfDeath : ∀ l, f l ≤ b l + 2 * (ε : ℝ) := by
    intro l
    have h1 : d l ≤ b l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hU.2 l
    have h2 : f l ≤ d l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hV.2 l
    linarith
  refine ⟨?_, ?_⟩
  · intro l
    have h1 : c l ≤ a l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hU.1 l
    have h2 : e l ≤ c l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hV.1 l
    change e l ≤ a l + ((ε + ε : ℝ≥0) : ℝ)
    rw [NNReal.coe_add]
    linarith
  · intro hdeath
    have hbad : ∀ l, f l ≤ a l + 2 * (ε : ℝ) := by
      intro l
      have h := hdeath l
      rw [CoordinateShift.translation_apply, NNReal.coe_add] at h
      linarith
    have hA : (∑ l, e l) < (∑ l, a l) + (n : ℝ) * (2 * (ε : ℝ)) -
        2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
      apply sum_lt_sum_add_const_sub (x := e) (y := a) j
        (2 * (ε : ℝ)) (2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)))
      · intro l
        linarith [heBirth l]
      · linarith [hbad j, hj']
    have hB : (∑ l, f l) < (∑ l, b l) + (n : ℝ) * (2 * (ε : ℝ)) -
        2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
      apply sum_lt_sum_add_const_sub (x := f) (y := b) i
        (2 * (ε : ℝ)) (2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)))
      · exact hfDeath
      · linarith [hbad i, hi']
    have hgap : 0 ≤ 4 *
        ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) -
          (n : ℝ) * (4 * (ε : ℝ)) := by
      rw [hρ]
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc
        0 ≤ 4 * ((n : ℝ) - 1) * (ε : ℝ) := by
          apply mul_nonneg
          · apply mul_nonneg
            · norm_num
            · linarith
          · exact ε.coe_nonneg
        _ = 4 * ((2 * (n : ℝ) - 1) * (ε : ℝ)) -
            (n : ℝ) * (4 * (ε : ℝ)) := by ring
    have hstrict : (∑ l, e l) + (∑ l, f l) <
        (∑ l, a l) + (∑ l, b l) := by linarith
    exact (not_lt_of_ge hα) hstrict

/-- Ordered significant finite hooks have a noncancelling two-step map. The
common active grade is derived from the endpoint bounds, significance, and the
endpoint-sum order, then the actual scalar coefficient product is used. -/
theorem finiteHook_composite_ne_zero_of_significant (hn : 0 < n) (ε : ℝ≥0)
    {a b c d e f : Fin n → ℝ} (hab : a < b) (hcd : c < d) (hef : e < f)
    (hα : (∑ i, a i) + (∑ i, b i) ≤ (∑ i, e i) + (∑ i, f i))
    (hR : finiteSignificant (RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε) ⟨(a, b), hab⟩)
    (hT : finiteSignificant (RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε) ⟨(e, f), hef⟩)
    (u : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) (hu : u ≠ 0)
    (v : Hook.module (k := k) c d ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) e f)) (hv : v ≠ 0) :
    u ≫ (CoordinateShift.shift ε).map v ≠ 0 := by
  classical
  have hnat : 1 ≤ 2 * n := by omega
  have hρ : (RectangleStabilityGeometry.stabilityRadius n ε : ℝ) =
      ((2 * (n : ℝ) - 1) * (ε : ℝ)) := by
    simp only [RectangleStabilityGeometry.stabilityRadius, NNReal.coe_mul,
      NNReal.coe_natCast, Nat.cast_sub hnat]
    push_cast
    ring
  have h2ρ : ((RectangleStabilityGeometry.stabilityRadius n ε +
      RectangleStabilityGeometry.stabilityRadius n ε : ℝ≥0) : ℝ) =
      2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
    simp [NNReal.coe_add]
    ring
  obtain ⟨i, hi⟩ := hR
  obtain ⟨j, hj⟩ := hT
  have hi' : b i > a i + 2 *
      ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
    simpa [h2ρ] using hi
  have hj' : f j > e j + 2 *
      ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
    simpa [h2ρ] using hj
  have hU := nonzero_finiteHook_map_endpoint_bounds hab ε u hu
  have hV := nonzero_finiteHook_map_endpoint_bounds hcd ε v hv
  have heBirth : ∀ l, e l ≤ a l + 2 * (ε : ℝ) := by
    intro l
    have h1 : c l ≤ a l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hU.1 l
    have h2 : e l ≤ c l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hV.1 l
    linarith
  have hfDeath : ∀ l, f l ≤ b l + 2 * (ε : ℝ) := by
    intro l
    have h1 : d l ≤ b l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hU.2 l
    have h2 : f l ≤ d l + (ε : ℝ) := by
      simpa only [CoordinateShift.translation_apply] using hV.2 l
    linarith
  have htarget : CoordinateShift.translation (ε + ε) a ∈ Hook.support e f := by
    refine ⟨?_, ?_⟩
    · intro l
      have h1 : c l ≤ a l + (ε : ℝ) := by
        simpa only [CoordinateShift.translation_apply] using hU.1 l
      have h2 : e l ≤ c l + (ε : ℝ) := by
        simpa only [CoordinateShift.translation_apply] using hV.1 l
      change e l ≤ a l + ((ε + ε : ℝ≥0) : ℝ)
      rw [NNReal.coe_add]
      linarith
    · intro hdeath
      have hbad : ∀ l, f l ≤ a l + 2 * (ε : ℝ) := by
        intro l
        have h := hdeath l
        rw [CoordinateShift.translation_apply, NNReal.coe_add] at h
        linarith
      have hA : (∑ l, e l) < (∑ l, a l) + (n : ℝ) * (2 * (ε : ℝ)) -
          2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
        apply sum_lt_sum_add_const_sub (x := e) (y := a) j
          (2 * (ε : ℝ))
          (2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) )
        · intro l
          have h := heBirth l
          linarith
        · have h := hbad j
          linarith
      have hB : (∑ l, f l) < (∑ l, b l) + (n : ℝ) * (2 * (ε : ℝ)) -
          2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) := by
        apply sum_lt_sum_add_const_sub (x := f) (y := b) i
          (2 * (ε : ℝ))
          (2 * ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)))
        · intro l
          exact hfDeath l
        · have hbad_i := hbad i
          linarith
      have hgap : 0 ≤ 4 *
          ((RectangleStabilityGeometry.stabilityRadius n ε : ℝ)) -
            (n : ℝ) * (4 * (ε : ℝ)) := by
        rw [hρ]
        have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        calc
          0 ≤ 4 * ((n : ℝ) - 1) * (ε : ℝ) := by
            apply mul_nonneg
            · apply mul_nonneg
              · norm_num
              · linarith
            · exact ε.coe_nonneg
          _ = 4 * ((2 * (n : ℝ) - 1) * (ε : ℝ)) -
              (n : ℝ) * (4 * (ε : ℝ)) := by ring
      have hstrict : (∑ l, e l) + (∑ l, f l) <
          (∑ l, a l) + (∑ l, b l) := by
        linarith
      exact (not_lt_of_ge hα) hstrict
  have htargetB := finiteHook_map_birth_active hab ε u hu
  have huCoeff := (finiteHookCoefficient_ne_zero_iff (k := k) hab ε u).2 hu
  have hvCoeff := (finiteHookCoefficient_ne_zero_iff (k := k) hcd ε v).2 hv
  have hcompCoeff := finiteHookCoefficient_composite_at (k := k) hab hcd ε
    u v le_rfl (Hook.birth_mem hab) htargetB htarget
  have hcoeffNe : finiteHookCoefficient (k := k) hab (ε + ε)
      (u ≫ (CoordinateShift.shift ε).map v ≫
        (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom) ≠ 0 := by
    rw [hcompCoeff]
    exact mul_ne_zero huCoeff hvCoeff
  intro hzero
  apply hcoeffNe
  have hcompZero : u ≫ (CoordinateShift.shift ε).map v ≫
      (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom = 0 := by
    have hcomp := congrArg
      (fun g => g ≫ (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom)
      hzero
    calc
      _ = 0 ≫ (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom := hcomp
      _ = 0 := by simp
  rw [hcompZero]
  change (0 : k) = 0
  rfl

/-- Coefficient multiplication for an ordered significant finite-hook path.
When either component map vanishes both sides are zero; otherwise the common
active grade is supplied by the endpoint geometry above. -/
theorem finiteHookCoefficient_composite_ordered (hn : 0 < n) (ε : ℝ≥0)
    {a b c d e f : Fin n → ℝ}
    (hab : a < b) (hcd : c < d) (hef : e < f)
    (hα : (∑ i, a i) + (∑ i, b i) ≤ (∑ i, e i) + (∑ i, f i))
    (hR : finiteSignificant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) ⟨(a, b), hab⟩)
    (hT : finiteSignificant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) ⟨(e, f), hef⟩)
    (u : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d))
    (v : Hook.module (k := k) c d ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) e f)) :
    finiteHookCoefficient (k := k) hab (ε + ε)
      (u ≫ (CoordinateShift.shift ε).map v ≫
        (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom) =
      finiteHookCoefficient (k := k) hab ε u *
        finiteHookCoefficient (k := k) hcd ε v := by
  by_cases hu : u = 0
  · subst u
    have hcomp : (0 ≫ (CoordinateShift.shift ε).map v ≫
        (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom) =
      (0 : Hook.module (k := k) a b ⟶
        (CoordinateShift.shift (ε + ε)).obj (Hook.module (k := k) e f)) := by simp
    rw [hcomp, finiteHookCoefficient_zero_aux (k := k) hab (ε + ε)]
    simp [finiteHookCoefficient_zero_aux (k := k) hab ε]
  by_cases hv : v = 0
  · subst v
    have hcomp : (u ≫ (CoordinateShift.shift ε).map (0 : _ ⟶
        (CoordinateShift.shift ε).obj (Hook.module (k := k) e f)) ≫
        (CoordinateShift.compIso ε ε (Hook.module (k := k) e f)).hom) =
      (0 : Hook.module (k := k) a b ⟶
        (CoordinateShift.shift (ε + ε)).obj (Hook.module (k := k) e f)) := by simp
    rw [hcomp, finiteHookCoefficient_zero_aux (k := k) hab (ε + ε),
      finiteHookCoefficient_zero_aux (k := k) hcd ε]
    simp
  have hpB := finiteHook_map_birth_active hab ε u hu
  have hpC := finiteHook_composite_birth_target_of_significant
    hn ε hab hcd hef hα hR hT u hu v hv
  exact finiteHookCoefficient_composite_at hab hcd ε u v le_rfl
    (Hook.birth_mem hab) hpB hpC

/-- The same-type hook coefficient respects two-step composition. When the
middle tag has the opposite type, one of the two maps is the vanishing
finite-to-principal block, so the product and composite coefficient are zero. -/
theorem tagScalar_composite (hn : 0 < n) (ε : ℝ≥0)
    {t s u : RealHookTag (n := n)}
    (hα : tagOrderValue t ≤ tagOrderValue u)
    (hT : tagSignificant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) t)
    (hU : tagSignificant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) u)
    (f : tagModule (k := k) t ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) s))
    (g : tagModule (k := k) s ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) u)) :
    tagScalar (k := k) (ε + ε) t u
      (f ≫ (CoordinateShift.shift ε).map g ≫
        (CoordinateShift.compIso ε ε (tagModule (k := k) u)).hom) =
      tagScalar (k := k) ε t s f * tagScalar (k := k) ε s u g := by
  cases t with
  | inl ab =>
    cases s with
    | inl cd =>
      cases u with
      | inl ef =>
        simpa [tagScalar, tagOrderValue, tagSignificant, tagModule,
          FiniteRankProjectiveClassification.rankProjectiveHookModule] using
          (finiteHookCoefficient_composite_ordered (k := k) hn ε ab.property
            cd.property ef.property (by simpa [tagOrderValue] using hα)
            (by simpa [tagSignificant] using hT)
            (by simpa [tagSignificant] using hU) f g)
      | inr e =>
        simp [tagScalar]
    | inr c =>
      cases u with
      | inl ef =>
        have hf : f = 0 := finiteHook_to_principal_zero ab.property ε f
        subst f
        have hcomp : (0 : tagModule (k := k) (.inl ab) ⟶
            (CoordinateShift.shift (ε + ε)).obj
              (tagModule (k := k) (.inl ef))) =
            (0 ≫ (CoordinateShift.shift ε).map g ≫
              (CoordinateShift.compIso ε ε
                (tagModule (k := k) (.inl ef))).hom) := by simp
        rw [← hcomp]
        change finiteHookCoefficient (k := k) ab.property (ε + ε)
            (0 : Hook.module (k := k) ab.val.1 ab.val.2 ⟶
              (CoordinateShift.shift (ε + ε)).obj
                (Hook.module (k := k) ef.val.1 ef.val.2)) =
          (0 : k) * 0
        rw [finiteHookCoefficient_zero_aux (k := k) ab.property (ε + ε)]
        simp
      | inr e =>
        simp [tagScalar]
  | inr a =>
    cases s with
    | inl cd =>
      cases u with
      | inl ef =>
        simp [tagScalar]
      | inr e =>
        have hg : g = 0 := finiteHook_to_principal_zero cd.property ε g
        subst g
        have hcomp : (f ≫ (CoordinateShift.shift ε).map
            (0 : tagModule (k := k) (.inl cd) ⟶
              (CoordinateShift.shift ε).obj (tagModule (k := k) (.inr e))) ≫
            (CoordinateShift.compIso ε ε
              (tagModule (k := k) (.inr e))).hom) =
            (0 : tagModule (k := k) (.inr a) ⟶
              (CoordinateShift.shift (ε + ε)).obj
                (tagModule (k := k) (.inr e))) := by simp
        rw [hcomp]
        change principalHookCoefficient (k := k) (ε + ε)
            (0 : HookInfinity.module (R := k) a ⟶
              (CoordinateShift.shift (ε + ε)).obj
                (HookInfinity.module (R := k) e)) = 0 * 0
        rw [principalHookCoefficient_zero]
        simp
    | inr c =>
      cases u with
      | inl ef =>
        simp [tagScalar]
      | inr e =>
        simpa [tagScalar, tagOrderValue, tagSignificant, tagModule,
          FiniteRankProjectiveClassification.rankProjectiveHookModule] using
          (principalHookCoefficient_composite (k := k) (ε := ε)
            (a := a) (c := c) (e := e) f g)

/-- A vanishing double-shift transition supplies the actual interleaving
maps with zero. -/
noncomputable def finiteInterleavingZero (ab : FiniteHookTag (n := n))
    (ρ : ℝ≥0)
    (h : CoordinateShift.transition (ρ + ρ)
      (Hook.module (k := k) ab.val.1 ab.val.2) = 0) :
    CoordinateInterleaving ρ (Hook.module (k := k) ab.val.1 ab.val.2) 0 where
  φ := 0
  ψ := 0
  φ_ψ := by simp [h]
  ψ_φ := by exact Subsingleton.elim _ _

/-- A finite hook is actually `ρ`-interleaved with zero exactly when its
double-shift transition vanishes, including the endpoint and `ρ = 0` cases. -/
theorem finiteInterleaved_zero_iff (ab : FiniteHookTag (n := n)) (ρ : ℝ≥0) :
    Nonempty (CoordinateInterleaving ρ
      (Hook.module (k := k) ab.val.1 ab.val.2) 0) ↔
        ¬ finiteSignificant (ρ + ρ) ab := by
  rw [finiteSignificant_iff_transition_ne_zero (k := k) (ρ + ρ) ab]
  simp only [not_not]
  constructor
  · rintro ⟨I⟩
    have hφ : I.φ = 0 := by
      apply NatTrans.ext
      funext p
      exact (Functor.zero_obj (C := Fin n → ℝ) (D := ModuleCat.{u} k)
        (CoordinateShift.translation ρ p)).eq_of_tgt _ _
    simpa [hφ] using I.φ_ψ.symm
  · intro h
    exact ⟨finiteInterleavingZero (k := k) ab ρ h⟩

@[simp] theorem finiteHookCoefficient_zero {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0) :
    finiteHookCoefficient (k := k) hab ε
      (0 : Hook.module (k := k) a b ⟶
        (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) = 0 := by
  classical
  unfold finiteHookCoefficient
  change (0 : k) = 0
  rfl

theorem finiteHookCoefficient_add {a b c d : Fin n → ℝ}
    (hab : a < b) (ε : ℝ≥0)
    (f g : Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d)) :
    finiteHookCoefficient (k := k) hab ε (f + g) =
      finiteHookCoefficient (k := k) hab ε f +
        finiteHookCoefficient (k := k) hab ε g := by
  simp only [finiteHookCoefficient, NatTrans.app_add, ModuleCat.hom_add,
    LinearMap.add_apply]
  exact (Submodule.subtype
    (SupportInterval.fiber (k := k) (Hook.support c d)
      (CoordinateShift.translation ε a))).map_add _ _

theorem finiteHookCoefficient_sum {a b c d : Fin n → ℝ} {ι : Type*}
    (hab : a < b) (ε : ℝ≥0) (A : Finset ι)
    (f : ι → (Hook.module (k := k) a b ⟶
      (CoordinateShift.shift ε).obj (Hook.module (k := k) c d))) :
    finiteHookCoefficient (k := k) hab ε (∑ i ∈ A, f i) =
      ∑ i ∈ A, finiteHookCoefficient (k := k) hab ε (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
      simp only [Finset.sum_insert hi, finiteHookCoefficient_add, ih]

/-- The diagonal hook coefficient is one whenever the double-shift transition
survives. -/
theorem finiteHookCoefficient_transition {ab : FiniteHookTag (n := n)}
    (δ : ℝ≥0) (h : finiteSignificant δ ab) :
    finiteHookCoefficient (k := k) ab.property δ
      (CoordinateShift.transition δ (Hook.module (k := k) ab.val.1 ab.val.2)) = 1 := by
  obtain ⟨i, hi⟩ := h
  let a := ab.val.1
  let b := ab.val.2
  have hactive : CoordinateShift.translation δ a ∈ Hook.support a b := by
    refine ⟨?_, ?_⟩
    · intro j
      change a j ≤ a j + (δ : ℝ)
      exact le_add_of_nonneg_right δ.coe_nonneg
    · intro hdeath
      exact (not_le_of_gt hi) (hdeath i)
  unfold finiteHookCoefficient
  change (structureMapLinear (Hook.module (k := k) a b)
    (show a ≤ CoordinateShift.translation δ a from fun j => by
      change a j ≤ a j + (δ : ℝ)
      exact le_add_of_nonneg_right δ.coe_nonneg)
    (SupportInterval.one (Hook.support a b) (Hook.birth_mem ab.property)) : k) = 1
  rw [SupportInterval.structureMap_val, if_pos hactive]
  rfl

private theorem finiteSignificant_of_le {δ ρ : ℝ≥0} (hδρ : δ ≤ ρ)
    {ab : FiniteHookTag (n := n)} (h : finiteSignificant ρ ab) :
    finiteSignificant δ ab := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  have hcast : (δ : ℝ) ≤ (ρ : ℝ) := hδρ
  exact lt_of_le_of_lt (add_le_add_right hcast _) hi

private theorem stabilityRadius_ge_epsilon (hn : 0 < n) (ε : ℝ≥0) :
    ε ≤ RectangleStabilityGeometry.stabilityRadius n ε := by
  have hnat : 1 ≤ 2 * n - 1 := by omega
  have hc : (1 : ℝ≥0) ≤ ((2 * n - 1 : ℕ) : ℝ≥0) := by exact_mod_cast hnat
  simpa only [one_mul, RectangleStabilityGeometry.stabilityRadius] using
    mul_le_mul_of_nonneg_right hc (show 0 ≤ ε from bot_le)

private def finiteHookNeighbor (ρ : ℝ≥0)
    (ab cd : FiniteHookTag (n := n)) : Prop :=
  Nonempty (CoordinateInterleaving ρ
    (Hook.module (k := k) ab.val.1 ab.val.2)
    (Hook.module (k := k) cd.val.1 cd.val.2))

private noncomputable def finiteHookNeighbors {ℓ : ℕ}
    (F : Fin ℓ → FiniteHookTag (n := n)) (A : Finset (Fin ℓ))
    (ρ : ℝ≥0) : Finset (Fin ℓ) :=
  Finset.univ.filter fun j => ∃ i ∈ A, finiteHookNeighbor (k := k) ρ (F i) (F j)

private def tagIsFinite (t : RealHookTag (n := n)) : Bool :=
  match t with
  | .inl _ => true
  | .inr _ => false

/-- For a source index set `A`, the neighbors in `G` at radius `ρ` are the
target occurrence indices `j` for which some `i ∈ A` has an actual coordinate
`ρ`-interleaving between the hook modules `tagModule (F i)` and
`tagModule (G j)`. Repeated tags remain separate occurrences. -/
noncomputable def tagNeighbors {ι κ : Type*} [Fintype κ]
    (F : ι → RealHookTag (n := n)) (G : κ → RealHookTag (n := n))
    (A : Finset ι) (ρ : ℝ≥0) : Finset κ :=
  Finset.univ.filter fun j => ∃ i ∈ A, tagNeighbor (k := k) ρ (F i) (G j)

private theorem tagScalar_sum {ι : Type*} (t s : RealHookTag (n := n))
    (ε : ℝ≥0) (A : Finset ι)
    (f : ι → (tagModule (k := k) t ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) s))) :
    tagScalar (k := k) ε t s (∑ i ∈ A, f i) =
      ∑ i ∈ A, tagScalar (k := k) ε t s (f i) := by
  cases t with
  | inl ab =>
    cases s with
    | inl cd =>
      change finiteHookCoefficient (k := k) ab.property ε (∑ i ∈ A, f i) =
        ∑ i ∈ A, finiteHookCoefficient (k := k) ab.property ε (f i)
      exact finiteHookCoefficient_sum (k := k) ab.property ε A f
    | inr c => simp [tagScalar]
  | inr a =>
    cases s with
    | inl cd => simp [tagScalar]
    | inr c =>
      change principalHookCoefficient (k := k) ε (∑ i ∈ A, f i) =
        ∑ i ∈ A, principalHookCoefficient (k := k) ε (f i)
      exact principalHookCoefficient_sum (k := k) ε A f

private theorem tagScalar_transition {ρ : ℝ≥0} {t : RealHookTag (n := n)}
    (h : tagSignificant (ρ + ρ) t) :
    tagScalar (k := k) (ρ + ρ) t t
      (CoordinateShift.transition (ρ + ρ) (tagModule (k := k) t)) = 1 := by
  cases t with
  | inl ab =>
    simpa [tagScalar, tagModule,
      FiniteRankProjectiveClassification.rankProjectiveHookModule] using
      (finiteHookCoefficient_transition (k := k) (ab := ab) (ρ + ρ) h)
  | inr a =>
    simpa [tagScalar, tagModule,
      FiniteRankProjectiveClassification.rankProjectiveHookModule] using
      (principalHookCoefficient_transition (k := k) (a := a) (ρ + ρ))

private theorem tagPathZeroOfNoNeighbors (hn : 0 < n)
    {t s u : RealHookTag (n := n)} (ε : ℝ≥0)
    (hα : tagOrderValue t ≤ tagOrderValue u)
    (hkind : tagIsFinite t = tagIsFinite u)
    (hts : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) t s)
    (hsu : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) s u)
    (f : tagModule (k := k) t ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) s))
    (g : tagModule (k := k) s ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) u)) :
    f ≫ (CoordinateShift.shift ε).map g = 0 := by
  cases t with
  | inl ab =>
    cases s with
    | inl cd =>
      cases u with
      | inl ef =>
        by_cases hf : f = 0
        · simp [hf]
        by_cases hg : g = 0
        · simp [hg]
        have hα' : (∑ l, ab.val.1 l) + (∑ l, ab.val.2 l) ≤
            (∑ l, ef.val.1 l) + (∑ l, ef.val.2 l) := by
          simpa [tagOrderValue] using hα
        rcases finite_hook_path_neighbor_of_maps (k := k) hn ε hα'
          ab.property f hf cd.property ef.property g hg with h | h
        · exact False.elim (hts (by simpa [tagNeighbor, tagModule,
            FiniteRankProjectiveClassification.rankProjectiveHookModule] using h))
        · exact False.elim (hsu (by simpa [tagNeighbor, tagModule,
            FiniteRankProjectiveClassification.rankProjectiveHookModule] using h))
      | inr e => simp [tagIsFinite] at hkind
    | inr c =>
      cases u with
      | inl ef =>
        have hf : f = 0 := finiteHook_to_principal_zero ab.property ε f
        rw [hf]
        simp
      | inr e => simp [tagIsFinite] at hkind
  | inr a =>
    cases s with
    | inl cd =>
      cases u with
      | inl ef => simp [tagIsFinite] at hkind
      | inr e =>
        have hg : g = 0 := finiteHook_to_principal_zero cd.property ε g
        rw [hg]
        simp
    | inr c =>
      cases u with
      | inl ef => simp [tagIsFinite] at hkind
      | inr e =>
        by_cases hf : f = 0
        · simp [hf]
        by_cases hg : g = 0
        · simp [hg]
        have hα' : (∑ l, a l) ≤ ∑ l, e l := by
          simpa [tagOrderValue] using hα
        have hpath := principal_hook_path_neighbor_of_maps (k := k) hn ε
          hα' f hf g hg
        exact False.elim (hts (by simpa [tagNeighbor, tagModule,
          FiniteRankProjectiveClassification.rankProjectiveHookModule] using hpath))

private theorem tagComponentPathZeroOutside (hn : 0 < n)
    {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (ε : ℝ≥0)
    (A : Finset (Fin m)) {i i' : Fin m} (hi : i ∈ A) (hi' : i' ∈ A)
    (hα : tagOrderValue (F i) ≤ tagOrderValue (F i'))
    {j : Fin ℓ} (hj : j ∉ tagNeighbors (k := k) F G A
      (RectangleStabilityGeometry.stabilityRadius n ε))
    (hkind : tagIsFinite (F i) = tagIsFinite (F i'))
    (f : tagModule (k := k) (F i) ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) (G j)))
    (g : tagModule (k := k) (G j) ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) (F i'))) :
    f ≫ (CoordinateShift.shift ε).map g = 0 := by
  have hts : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) (F i) (G j) := by
    intro h
    apply hj
    simp only [tagNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, h⟩
  have hsu : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) (G j) (F i') := by
    intro h
    apply hj
    simp only [tagNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    have h' : tagNeighbor (k := k)
        (RectangleStabilityGeometry.stabilityRadius n ε) (F i') (G j) := by
      rcases h with ⟨I⟩
      exact ⟨I.symm⟩
    exact ⟨i', hi', h'⟩
  exact tagPathZeroOfNoNeighbors (k := k) hn ε hα hkind hts hsu f g

private theorem tagScalarPathZeroOfNoNeighbors (hn : 0 < n)
    {t s u : RealHookTag (n := n)} (ε : ℝ≥0)
    (hα : tagOrderValue t ≤ tagOrderValue u)
    (hts : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) t s)
    (hsu : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) s u)
    (f : tagModule (k := k) t ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) s))
    (g : tagModule (k := k) s ⟶
      (CoordinateShift.shift ε).obj (tagModule (k := k) u)) :
    tagScalar (k := k) (ε + ε) t u
      (f ≫ (CoordinateShift.shift ε).map g ≫
        (CoordinateShift.compIso ε ε (tagModule (k := k) u)).hom) = 0 := by
  cases t with
  | inl ab =>
    cases u with
    | inl ef =>
      have hpath := tagPathZeroOfNoNeighbors (k := k) hn ε hα rfl hts hsu f g
      have hcomp : f ≫ (CoordinateShift.shift ε).map g ≫
          (CoordinateShift.compIso ε ε (tagModule (k := k) (.inl ef))).hom = 0 := by
        calc
          _ = 0 ≫ (CoordinateShift.compIso ε ε
              (tagModule (k := k) (.inl ef))).hom :=
            congrArg (fun q => q ≫ (CoordinateShift.compIso ε ε
              (tagModule (k := k) (.inl ef))).hom) hpath
          _ = 0 := zero_comp
      rw [hcomp]
      exact tagScalar_zero (k := k) (ε + ε) (.inl ab) (.inl ef)
    | inr e => simp [tagScalar]
  | inr a =>
    cases u with
    | inl ef => simp [tagScalar]
    | inr e =>
      have hpath := tagPathZeroOfNoNeighbors (k := k) hn ε hα rfl hts hsu f g
      have hcomp : f ≫ (CoordinateShift.shift ε).map g ≫
          (CoordinateShift.compIso ε ε (tagModule (k := k) (.inr e))).hom = 0 := by
        calc
          _ = 0 ≫ (CoordinateShift.compIso ε ε
              (tagModule (k := k) (.inr e))).hom :=
            congrArg (fun q => q ≫ (CoordinateShift.compIso ε ε
              (tagModule (k := k) (.inr e))).hom) hpath
          _ = 0 := zero_comp
      rw [hcomp]
      exact tagScalar_zero (k := k) (ε + ε) (.inr a) (.inr e)

private theorem tagScalarComponentPathZeroOutside (hn : 0 < n)
    {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (ε : ℝ≥0) (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G)) (A : Finset (Fin m))
    {i i' : Fin m} (hi : i ∈ A) (hi' : i' ∈ A)
    (hα : tagOrderValue (F i) ≤ tagOrderValue (F i'))
    {j : Fin ℓ} (hj : j ∉ tagNeighbors (k := k) F G A
      (RectangleStabilityGeometry.stabilityRadius n ε)) :
    tagScalar (k := k) (ε + ε) (F i) (F i')
      (component (k := k) F G ε I.φ i j ≫
        (CoordinateShift.shift ε).map
          (component (k := k) G F ε I.ψ j i') ≫
        (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) = 0 := by
  have hts : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) (F i) (G j) := by
    intro h
    apply hj
    simp only [tagNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, h⟩
  have hsu : ¬ tagNeighbor (k := k)
      (RectangleStabilityGeometry.stabilityRadius n ε) (G j) (F i') := by
    intro h
    apply hj
    simp only [tagNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h with ⟨I⟩
    exact ⟨i', hi', ⟨I.symm⟩⟩
  exact tagScalarPathZeroOfNoNeighbors (k := k) hn ε hα hts hsu
    (component (k := k) F G ε I.φ i j)
    (component (k := k) G F ε I.ψ j i')

private theorem tagScalarSumNeighbors (hn : 0 < n)
    {m ℓ : ℕ}
    (F : Fin m → RealHookTag (n := n)) (G : Fin ℓ → RealHookTag (n := n))
    (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G))
    (A : Finset (Fin m)) {i i' : Fin m} (hi : i ∈ A) (hi' : i' ∈ A)
    (hα : tagOrderValue (F i) ≤ tagOrderValue (F i')) :
    ∑ j ∈ tagNeighbors (k := k) F G A
        (RectangleStabilityGeometry.stabilityRadius n ε),
      tagScalar (k := k) (ε + ε) (F i) (F i')
        (component (k := k) F G ε I.φ i j ≫
          (CoordinateShift.shift ε).map
            (component (k := k) G F ε I.ψ j i') ≫
          (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) =
      tagScalar (k := k) (ε + ε) (F i) (F i')
        ((∑ j : Fin ℓ,
          component (k := k) F G ε I.φ i j ≫
            (CoordinateShift.shift ε).map
              (component (k := k) G F ε I.ψ j i')) ≫
          (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) := by
  classical
  let B := tagNeighbors (k := k) F G A
    (RectangleStabilityGeometry.stabilityRadius n ε)
  change (∑ j ∈ B,
      tagScalar (k := k) (ε + ε) (F i) (F i')
        (component (k := k) F G ε I.φ i j ≫
          (CoordinateShift.shift ε).map
            (component (k := k) G F ε I.ψ j i') ≫
          (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom)) = _
  calc
    _ = ∑ j : Fin ℓ,
        tagScalar (k := k) (ε + ε) (F i) (F i')
          (component (k := k) F G ε I.φ i j ≫
            (CoordinateShift.shift ε).map
              (component (k := k) G F ε I.ψ j i') ≫
            (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) := by
      apply Finset.sum_subset (Finset.subset_univ B)
      intro j _ hj
      exact tagScalarComponentPathZeroOutside (k := k) hn F G ε I A hi hi'
        hα hj
    _ = tagScalar (k := k) (ε + ε) (F i) (F i')
        ((∑ j : Fin ℓ,
          component (k := k) F G ε I.φ i j ≫
            (CoordinateShift.shift ε).map
              (component (k := k) G F ε I.ψ j i')) ≫
          (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) := by
      rw [Preadditive.sum_comp, tagScalar_sum]
      simp only [Category.assoc]

private theorem tagSignificant_of_le {δ ρ : ℝ≥0} (hδρ : δ ≤ ρ)
    {t : RealHookTag (n := n)} (h : tagSignificant ρ t) :
    tagSignificant δ t := by
  cases t with
  | inl ab => exact finiteSignificant_of_le hδρ h
  | inr a => trivial

private theorem tagNeighbor_symm {ρ : ℝ≥0} {t s : RealHookTag (n := n)}
    (h : tagNeighbor (k := k) ρ t s) : tagNeighbor (k := k) ρ s t := by
  rcases h with ⟨I⟩
  exact ⟨I.symm⟩

/-- Hall's cardinality bound over a field and for `0 < n` is as follows. Put
`ρ := RectangleStabilityGeometry.stabilityRadius n ε`. An actual coordinate
`ε`-interleaving between the finite hook-family modules `familyModule F` and
`familyModule G` implies
`A.card ≤ (tagNeighbors F G A ρ).card` whenever every `i ∈ A` satisfies
`tagSignificant (ρ + ρ) (F i)`. The family interleaving is the hypothesis;
membership in `tagNeighbors` is still defined by an actual coordinate
`ρ`-interleaving between individual hook modules. -/
theorem card_le_neighbors (hn : 0 < n)
    {m ℓ : ℕ} (F : Fin m → RealHookTag (n := n))
    (G : Fin ℓ → RealHookTag (n := n)) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G)) (A : Finset (Fin m))
    (hA : ∀ i ∈ A, tagSignificant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) (F i)) :
    A.card ≤ (tagNeighbors (k := k) F G A
      (RectangleStabilityGeometry.stabilityRadius n ε)).card := by
  classical
  let ρ := RectangleStabilityGeometry.stabilityRadius n ε
  let B := tagNeighbors (k := k) F G A ρ
  let key (i : A) : ℝ ×ₗ Fin (Fintype.card A) :=
    toLex (tagOrderValue (F i), (Fintype.equivFin A) i)
  let ord : LinearOrder A := LinearOrder.lift' key (by
    intro i j hij
    apply (Fintype.equivFin A).injective
    exact congrArg (fun z => (ofLex z).2) hij)
  letI : LinearOrder A := ord
  letI : LE A := ord.toPartialOrder.toPreorder.toLE
  letI : LT A := ord.toPartialOrder.toPreorder.toLT
  have hα {i i' : A} (h : i ≤ i') :
      tagOrderValue (F i) ≤ tagOrderValue (F i') := by
    change key i ≤ key i' at h
    exact Prod.Lex.monotone_fst _ _ h
  let Fm : Matrix B A k := fun j i => tagScalar (k := k) ε (F i) (G j)
    (component (k := k) F G ε I.φ i j)
  let Gm : Matrix A B k := fun i j => tagScalar (k := k) ε (G j) (F i)
    (component (k := k) G F ε I.ψ j i)
  have hε : ε ≤ ρ := by
    dsimp [ρ]
    exact stabilityRadius_ge_epsilon hn ε
  have hεε : ε + ε ≤ ρ + ρ := add_le_add hε hε
  have entry (i i' : A) (h : tagOrderValue (F i) ≤ tagOrderValue (F i')) :
      (Gm * Fm) i' i = tagScalar (k := k) (ε + ε) (F i) (F i')
        ((∑ j : Fin ℓ,
          component (k := k) F G ε I.φ i j ≫
            (CoordinateShift.shift ε).map
              (component (k := k) G F ε I.ψ j i')) ≫
          (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) := by
    calc
      (Gm * Fm) i' i = ∑ j ∈ B,
          tagScalar (k := k) ε (F i) (G j)
            (component (k := k) F G ε I.φ i j) *
          tagScalar (k := k) ε (G j) (F i')
            (component (k := k) G F ε I.ψ j i') := by
        change (∑ j : B,
          tagScalar (k := k) ε (G j) (F i')
            (component (k := k) G F ε I.ψ j i') *
          tagScalar (k := k) ε (F i) (G j)
            (component (k := k) F G ε I.φ i j)) = _
        calc
          _ = ∑ j ∈ B,
              tagScalar (k := k) ε (G j) (F i')
                (component (k := k) G F ε I.ψ j i') *
              tagScalar (k := k) ε (F i) (G j)
                (component (k := k) F G ε I.φ i j) :=
            Finset.sum_coe_sort B _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            exact mul_comm _ _
      _ = ∑ j ∈ B,
          tagScalar (k := k) (ε + ε) (F i) (F i')
            (component (k := k) F G ε I.φ i j ≫
              (CoordinateShift.shift ε).map
                (component (k := k) G F ε I.ψ j i') ≫
              (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (tagScalar_composite (k := k) hn ε h
          (hA i.val i.property)
          (hA i'.val i'.property)
          (component (k := k) F G ε I.φ i j)
          (component (k := k) G F ε I.ψ j i')).symm
      _ = tagScalar (k := k) (ε + ε) (F i) (F i')
          ((∑ j : Fin ℓ,
            component (k := k) F G ε I.φ i j ≫
              (CoordinateShift.shift ε).map
                (component (k := k) G F ε I.ψ j i')) ≫
            (CoordinateShift.compIso ε ε (tagModule (k := k) (F i'))).hom) := by
        exact tagScalarSumNeighbors (k := k) hn F G ε I A i.property i'.property
          h
  have hbelow : ∀ ⦃i i' : A⦄, i' < i → (Gm * Fm) i i' = 0 := by
    intro i i' h
    have hle : @LE.le A ord.toPartialOrder.toPreorder.toLE i' i :=
      ((@Preorder.lt_iff_le_not_ge A ord.toPartialOrder.toPreorder i' i).mp h).1
    have hne : i' ≠ i := by
      intro heq
      have hlt := (@Preorder.lt_iff_le_not_ge A ord.toPartialOrder.toPreorder
        i' i).mp h
      apply hlt.2
      simpa [heq] using (ord.toPartialOrder.toPreorder.le_refl i)
    rw [entry i' i (hα hle),
      component_interleaving_sum_ne F G ε I
        (show (i' : Fin m) ≠ (i : Fin m) from fun he => hne (Subtype.ext he))]
    simp
  have hdiag (i : A) : (Gm * Fm) i i = 1 := by
    rw [entry i i (hα (ord.toPartialOrder.toPreorder.le_refl i)),
      component_interleaving_sum_self F G ε I i.val]
    exact tagScalar_transition
      (tagSignificant_of_le hεε (hA i.val i.property))
  have hc := RectangleHall.card_le_of_triangular_product Gm Fm hbelow hdiag
  simpa only [Fintype.card_coe, B] using hc

/-- Every hook significant at the `(2n-1)ε` threshold has a distinct
`(2n-1)ε`-interleaved partner on the opposite side. The actual finite-sum
interleaving supplies the Hall inequalities; they are not assumptions. -/
theorem exists_significant_injection (hn : 0 < n)
    {m ℓ : ℕ} (F : Fin m → RealHookTag (n := n))
    (G : Fin ℓ → RealHookTag (n := n)) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G)) :
    ∃ f : {i // tagSignificant
        (RectangleStabilityGeometry.stabilityRadius n ε +
          RectangleStabilityGeometry.stabilityRadius n ε) (F i)} → Fin ℓ,
      Function.Injective f ∧ ∀ i, tagNeighbor (k := k)
        (RectangleStabilityGeometry.stabilityRadius n ε) (F i.val) (G (f i)) := by
  classical
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (i : {i // tagSignificant
        (RectangleStabilityGeometry.stabilityRadius n ε +
          RectangleStabilityGeometry.stabilityRadius n ε) (F i)}) (j : Fin ℓ) =>
      tagNeighbor (k := k) (RectangleStabilityGeometry.stabilityRadius n ε)
        (F i.val) (G j))).mp
  intro A
  let A' : Finset (Fin m) := A.image Subtype.val
  have hA : ∀ i ∈ A', tagSignificant
      (RectangleStabilityGeometry.stabilityRadius n ε +
        RectangleStabilityGeometry.stabilityRadius n ε) (F i) := by
    intro i hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact a.property
  have h := card_le_neighbors (k := k) hn F G ε I A' hA
  have he : tagNeighbors (k := k) F G A'
      (RectangleStabilityGeometry.stabilityRadius n ε) =
      Finset.univ.filter (fun j => ∃ a ∈ A,
        tagNeighbor (k := k) (RectangleStabilityGeometry.stabilityRadius n ε)
          (F a.val) (G j)) := by
    ext j
    simp [tagNeighbors, A']
  rw [he, Finset.card_image_of_injective A Subtype.val_injective] at h
  exact h

private theorem tagInterleavedZero_of_not_significant
    (t : RealHookTag (n := n)) (ρ : ℝ≥0)
    (h : ¬ tagSignificant (ρ + ρ) t) :
    Nonempty (CoordinateInterleaving ρ (tagModule (k := k) t) 0) := by
  cases t with
  | inl ab =>
    exact (finiteInterleaved_zero_iff (k := k) ab ρ).mpr
      (by simpa [tagSignificant] using h)
  | inr a => exact False.elim (h trivial)

/-- An actual ε-interleaving of finite occurrence-indexed hook sums yields one
partial matching at radius `(2n-1)ε`. Paired entries and every deletion on
either side carry actual coordinate interleavings. Repeated tags remain
separate occurrences, principal-upset supports are included, and the zero
boundary is settled from the rank-exact multiplicity theorem. -/
theorem exists_matching (hn : 0 < n)
    {m ℓ : ℕ} (F : Fin m → RealHookTag (n := n))
    (G : Fin ℓ → RealHookTag (n := n)) (ε : ℝ≥0)
    (I : CoordinateInterleaving ε (familyModule (k := k) F)
      (familyModule (k := k) G)) :
    ∃ M : OccurrenceMatching (Fin m) (Fin ℓ) PEmpty.{1} PEmpty.{1},
      IsMatching (k := k) (RectangleStabilityGeometry.stabilityRadius n ε) F G M := by
  classical
  by_cases hε : ε = 0
  · subst ε
    simpa [RectangleStabilityGeometry.stabilityRadius] using
      exists_matching_of_zero_interleaving (k := k) F G I
  · let ρ := RectangleStabilityGeometry.stabilityRadius n ε
    let P := fun i => tagSignificant (ρ + ρ) (F i)
    let Q := fun j => tagSignificant (ρ + ρ) (G j)
    obtain ⟨f, hf, hfr⟩ := exists_significant_injection (k := k) hn F G ε I
    obtain ⟨g, hg, hgr⟩ := exists_significant_injection (k := k) hn G F ε I.symm
    obtain ⟨M, hp, hs, ht⟩ :=
      FiniteOccurrenceMatching.exists_two_sided P Q
        (fun i j => tagNeighbor (k := k) ρ (F i) (G j))
        f hf hfr g hg (fun j => tagNeighbor_symm (k := k) (hgr j))
    refine ⟨M, hp, ?_, ?_⟩
    · intro i hi
      apply tagInterleavedZero_of_not_significant (k := k) (F i) ρ
      intro hsig
      obtain ⟨j, hj⟩ := hs i hsig
      simp [hi] at hj
    · intro i hi
      apply tagInterleavedZero_of_not_significant (k := k) (G i) ρ
      intro hsig
      obtain ⟨j, hj⟩ := ht i hsig
      exact hi j hj

private def sampleFiniteTag : RealHookTag (n := 1) :=
  .inl ⟨(fun _ => (0 : ℝ), fun _ => (1 : ℝ)), by
    change (∀ i : Fin 1, (0 : ℝ) ≤ 1) ∧ ¬ ∀ i : Fin 1, (1 : ℝ) ≤ 0
    constructor
    · intro i; norm_num
    · intro h
      have := h 0
      norm_num at this⟩

private def samplePrincipalTag : RealHookTag (n := 1) := .inr fun _ => (0 : ℝ)

example {k : Type} [Field k] :
    ∃ M : OccurrenceMatching (Fin 2) (Fin 2) PEmpty.{1} PEmpty.{1},
      IsMatching (k := k) 0 (fun _ => sampleFiniteTag) (fun _ => sampleFiniteTag) M :=
  by simpa [RectangleStabilityGeometry.stabilityRadius] using
    (exists_matching (k := k) (n := 1) (by omega) (fun _ => sampleFiniteTag)
    (fun _ => sampleFiniteTag)
    0 (CoordinateInterleaving.ofIso (Iso.refl _)))

example {k : Type} [Field k] :
    ∃ M : OccurrenceMatching (Fin 1) (Fin 1) PEmpty.{1} PEmpty.{1},
      IsMatching (k := k) 0 (fun _ => samplePrincipalTag) (fun _ => samplePrincipalTag) M :=
  by simpa [RectangleStabilityGeometry.stabilityRadius] using
    (exists_matching (k := k) (n := 1) (by omega) (fun _ => samplePrincipalTag)
    (fun _ => samplePrincipalTag)
    0 (CoordinateInterleaving.ofIso (Iso.refl _)))

example {k : Type} [Field k] :
    ∃ M : OccurrenceMatching (Fin 0) (Fin 0) PEmpty.{1} PEmpty.{1},
      IsMatching (k := k) 0 (Fin.elim0 : Fin 0 → RealHookTag (n := 1))
        (Fin.elim0 : Fin 0 → RealHookTag (n := 1)) M :=
  by simpa [RectangleStabilityGeometry.stabilityRadius] using
    (exists_matching (k := k) (n := 1) (by omega)
    (Fin.elim0 : Fin 0 → RealHookTag (n := 1))
    (Fin.elim0 : Fin 0 → RealHookTag (n := 1))
    0 (CoordinateInterleaving.ofIso (Iso.refl _)))

end TDA.Persistence.HookMatching
