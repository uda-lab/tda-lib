import TDA.Persistence.RankProjective
import TDA.Persistence.RankExactIso
import TDA.Persistence.RealCoordinates
import TDA.Persistence.CoordinateShift
import Mathlib.Tactic

/-!
# Euler formula for finite rank-exact resolutions

For a supplied finite family of rank-exact short exact rows, the rank of each
structure map is the alternating sum of the corresponding ranks of the middle
terms. The proof uses the rank-additivity equation in every row and cancels the
successive kernel terms. Finite rank-exact projective resolutions are an
additional structured input for this row-only identity.
-/

set_option autoImplicit false

universe u v

namespace TDA.Persistence

open CategoryTheory
open scoped ZeroObject

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- The finrank of the image of a persistence-module structure map. On pointwise
finite-dimensional modules this is its usual rank. For an infinite-dimensional image,
Mathlib's `Module.finrank` convention gives zero, so the rank invariant interpretation
used below is in the finite-dimensional scope guaranteed by the rank-exact rows and
endpoint isomorphisms. -/
noncomputable def rankOfStructureMap (M : PModule.{u,v,u} k P) {a b : P}
    (hab : a ≤ b) : ℕ :=
  Module.finrank k (LinearMap.range (structureMapLinear M hab))

@[simp] theorem rankOfStructureMap_zero {a b : P} (hab : a ≤ b) :
    rankOfStructureMap (0 : PModule.{u,v,u} k P) hab = 0 := by
  unfold rankOfStructureMap
  have htarget : Subsingleton ((0 : PModule.{u,v,u} k P).obj b) :=
    ModuleCat.subsingleton_of_isZero (Functor.zero_obj b)
  have hrange : Subsingleton
      (LinearMap.range (structureMapLinear (0 : PModule.{u,v,u} k P) hab)) :=
    ⟨fun x y => Subtype.ext (htarget.elim x.val y.val)⟩
  exact @Module.finrank_zero_of_subsingleton k _ _ _ _ _ hrange

/-- Natural isomorphisms preserve the ranks of corresponding structure maps. -/
theorem rankOfStructureMap_iso {M N : PModule.{u,v,u} k P} {a b : P}
    (hab : a ≤ b) (e : M ≅ N) :
    rankOfStructureMap M hab = rankOfStructureMap N hab := by
  let ea : M.obj a ≃ₗ[k] N.obj a := (e.app a).toLinearEquiv
  let eb : M.obj b ≃ₗ[k] N.obj b := (e.app b).toLinearEquiv
  have hnat : (structureMapLinear N hab).comp ea.toLinearMap =
      eb.toLinearMap.comp (structureMapLinear M hab) := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun f : M.obj a ⟶ N.obj b => f.hom x)
      (e.hom.naturality (homOfLE hab))
    change (e.app b).toLinearEquiv (structureMapLinear M hab x) =
      structureMapLinear N hab ((e.app a).toLinearEquiv x) at h
    exact h.symm
  have hrange := congrArg LinearMap.range hnat
  have hleft : LinearMap.range (eb.toLinearMap.comp (structureMapLinear M hab)) =
      Submodule.map eb.toLinearMap (LinearMap.range (structureMapLinear M hab)) :=
    LinearMap.range_comp _ _
  have hsurj : LinearMap.range ea.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr ea.surjective
  rw [LinearMap.range_comp_of_range_eq_top _ hsurj, hleft] at hrange
  calc
    rankOfStructureMap M hab =
        Module.finrank k (Submodule.map eb.toLinearMap
          (LinearMap.range (structureMapLinear M hab))) := by
      unfold rankOfStructureMap
      exact (LinearEquiv.finrank_map_eq eb _).symm
    _ = rankOfStructureMap N hab := by
      unfold rankOfStructureMap
      rw [← hrange]

/-- A finite family of actual rank-exact rows, retaining each indexed term as an occurrence.

For `i : Fin length`, the actual row is
`0 → kernel (i.succ) → term i → kernel (i.castSucc) → 0`.
The endpoint isomorphisms identify `kernel 0` with the resolved module and the
last kernel with zero. -/
structure FiniteRankExactResolution (M : PModule.{u,v,u} k P) where
  length : ℕ
  kernel : Fin (length + 1) → PModule.{u,v,u} k P
  term : Fin length → PModule.{u,v,u} k P
  inclusion : ∀ i, kernel i.succ ⟶ term i
  quotient : ∀ i, term i ⟶ kernel i.castSucc
  row_rank_exact : ∀ i, IsRankExact (inclusion i) (quotient i)
  initial_iso : kernel 0 ≅ M
  terminal_iso : kernel (Fin.last length) ≅ 0

/-! A projective resolution adds projectivity of each indexed middle term. The existing
`IsRankProjective` API is formulated for partial orders on a universe-zero index type. -/
structure FiniteRankProjectiveResolution {P : Type} [PartialOrder P]
    (M : PModule.{u,0,u} k P) extends FiniteRankExactResolution M where
  term_rank_projective : ∀ i, IsRankProjective (term i)

namespace FiniteRankExactResolution

variable {M : PModule.{u,v,u} k P}

private theorem alternatingRowSum :
    ∀ (m : ℕ) (r : Fin (m + 1) → ℤ) (q : Fin m → ℤ),
      (∀ i, q i = r i.succ + r i.castSucc) →
      (∑ i : Fin m, (-1 : ℤ) ^ i.val * q i) =
        r 0 - (-1 : ℤ) ^ m * r (Fin.last m) := by
  intro m
  induction m with
  | zero =>
      intro r q _
      simp
  | succ m ih =>
      intro r q hrow
      let r' : Fin (m + 1) → ℤ := fun i => r i.succ
      let q' : Fin m → ℤ := fun i => q i.succ
      have hrow' : ∀ i, q' i = r' i.succ + r' i.castSucc := by
        intro i
        dsimp [q', r']
        simpa using hrow i.succ
      have htail := ih r' q' hrow'
      have hsign :
          (∑ i : Fin m, (-1 : ℤ) ^ i.succ.val * q i.succ) =
            -(∑ i : Fin m, (-1 : ℤ) ^ i.val * q' i) := by
        calc
          _ = ∑ i : Fin m, -((-1 : ℤ) ^ i.val * q' i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [q', Fin.val_succ, pow_succ, mul_comm]
          _ = _ := by rw [Finset.sum_neg_distrib]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul]
      rw [hrow 0, hsign, htail]
      simp [r', Fin.castSucc_zero, Fin.succ_last, pow_succ, mul_comm]
      ring

/-- For every `a ≤ b`, the module rank is the integer alternating sum of the indexed
middle-term ranks. The equality follows by applying `IsRankExact.rank_add` to every actual
row and telescoping the kernel ranks. -/
theorem rank_eq_alternating_sum (R : FiniteRankExactResolution M)
    {a b : P} (hab : a ≤ b) :
    (rankOfStructureMap M hab : ℤ) =
      ∑ i : Fin R.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (R.term i) hab : ℤ) := by
  let r : Fin (R.length + 1) → ℤ := fun i =>
    (rankOfStructureMap (R.kernel i) hab : ℤ)
  let q : Fin R.length → ℤ := fun i =>
    (rankOfStructureMap (R.term i) hab : ℤ)
  have hrow : ∀ i, q i = r i.succ + r i.castSucc := by
    intro i
    dsimp [q, r, rankOfStructureMap]
    exact_mod_cast (R.row_rank_exact i).rank_add hab
  have hsum := alternatingRowSum R.length r q hrow
  have hstart : r 0 = (rankOfStructureMap M hab : ℤ) := by
    dsimp [r]
    exact_mod_cast rankOfStructureMap_iso hab R.initial_iso
  have hfinish : r (Fin.last R.length) = 0 := by
    dsimp [r]
    rw [rankOfStructureMap_iso hab R.terminal_iso]
    simp
  rw [hstart, hfinish] at hsum
  simp only [mul_zero, sub_zero] at hsum
  exact hsum.symm

end FiniteRankExactResolution

namespace FiniteRankProjectiveResolution

variable {P : Type} [PartialOrder P] {M : PModule.{u,0,u} k P}

/-- The Euler formula for a finite rank-exact projective resolution. -/
theorem rank_eq_alternating_sum (R : FiniteRankProjectiveResolution M)
    {a b : P} (hab : a ≤ b) :
    (rankOfStructureMap M hab : ℤ) =
      ∑ i : Fin R.length, (-1 : ℤ) ^ i.val *
        (rankOfStructureMap (R.term i) hab : ℤ) :=
  FiniteRankExactResolution.rank_eq_alternating_sum
    R.toFiniteRankExactResolution hab

end FiniteRankProjectiveResolution

section RealCoordinateOperations

open CategoryTheory.Limits
open scoped TDA.Persistence NNReal
variable {n : ℕ}

private def translationNeg (ε : ℝ≥0) : (Fin n → ℝ) →o (Fin n → ℝ) where
  toFun a := fun i => a i - (ε : ℝ)
  monotone' a b h i := by
    change a i - (ε : ℝ) ≤ b i - (ε : ℝ)
    exact sub_le_sub_right (h i) _

private def shiftNeg (ε : ℝ≥0) :
    PModule.{u,0,u} k (Fin n → ℝ) ⥤ PModule.{u,0,u} k (Fin n → ℝ) where
  obj M := reindex (translationNeg ε) M
  map f := reindexNatTrans (translationNeg ε) f
  map_id := by intros; rfl
  map_comp := by intros; rfl

private theorem orderFunctor_map_eqToHom {P Q : Type} [Preorder P] [Preorder Q]
    (f : P →o Q) {a b : P} (h : a = b) :
    f.toFunctor.map (eqToHom h) = eqToHom (congrArg f h) := by
  cases h
  rfl

private def reindexIsoOfEq {α β : (Fin n → ℝ) →o (Fin n → ℝ)}
    (h : ∀ p, α p = β p) (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    reindex α M ≅ reindex β M :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun p => eqToIso (h p)) (by intros; apply Subsingleton.elim)) M

@[simp] private theorem reindexIsoOfEq_hom_app
    {α β : (Fin n → ℝ) →o (Fin n → ℝ)} (h : ∀ p, α p = β p)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (reindexIsoOfEq h M).hom.app p = M.map (eqToHom (h p)) := rfl

@[simp] private theorem reindexIsoOfEq_inv_app
    {α β : (Fin n → ℝ) →o (Fin n → ℝ)} (h : ∀ p, α p = β p)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (reindexIsoOfEq h M).inv.app p = M.map (eqToHom (h p).symm) := rfl

private theorem translationPosNeg_orderIso (ε : ℝ≥0) :
    (CoordinateShift.translation ε).comp (translationNeg (n := n) ε) =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) := by
  apply OrderHom.ext
  funext p
  funext i
  change (p i - (ε : ℝ)) + (ε : ℝ) = p i
  ring

private theorem translationNegPos_orderIso (ε : ℝ≥0) :
    (translationNeg (n := n) ε).comp (CoordinateShift.translation ε) =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) := by
  apply OrderHom.ext
  funext p
  funext i
  change (p i + (ε : ℝ)) - (ε : ℝ) = p i
  ring

private theorem translationPosNeg_eq_id (ε : ℝ≥0) (p : Fin n → ℝ) :
    (CoordinateShift.translation ε).comp (translationNeg (n := n) ε) p = p := by
  simpa using congrArg (fun f : (Fin n → ℝ) →o (Fin n → ℝ) => f p)
    (translationPosNeg_orderIso (n := n) ε)

private theorem translationNegPos_eq_id (ε : ℝ≥0) (p : Fin n → ℝ) :
    (translationNeg (n := n) ε).comp (CoordinateShift.translation ε) p = p := by
  simpa using congrArg (fun f : (Fin n → ℝ) →o (Fin n → ℝ) => f p)
    (translationNegPos_orderIso (n := n) ε)

private theorem translationPosNeg_eq_id' (ε : ℝ≥0) :
    ∀ p, (CoordinateShift.translation ε).comp (translationNeg (n := n) ε) p =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p := by
  intro p
  simpa using translationPosNeg_eq_id (n := n) ε p

private theorem translationNegPos_eq_id' (ε : ℝ≥0) :
    ∀ p, (translationNeg (n := n) ε).comp (CoordinateShift.translation ε) p =
      (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p := by
  intro p
  simpa using translationNegPos_eq_id (n := n) ε p

private theorem reindexIsoOfEq_naturality {α β : (Fin n → ℝ) →o (Fin n → ℝ)}
    (h : ∀ p, α p = β p) {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (f : M ⟶ N) :
    (reindexIsoOfEq h M).hom ≫ reindexNatTrans β f =
      reindexNatTrans α f ≫ (reindexIsoOfEq h N).hom := by
  apply NatTrans.ext
  funext p
  change M.map (eqToHom (h p)) ≫ f.app (β p) =
    f.app (α p) ≫ N.map (eqToHom (h p))
  exact f.naturality (eqToHom (h p))

private def shiftNegPosNatIso (ε : ℝ≥0) :
    CoordinateShift.shift ε ⋙ shiftNeg (k := k) (n := n) ε ≅ 𝟭 _ := by
  let h := translationPosNeg_eq_id' (n := n) ε
  refine NatIso.ofComponents (fun M => ?_) ?_
  · change reindex ((CoordinateShift.translation ε).comp
      (translationNeg (n := n) ε)) M ≅ reindex OrderHom.id M
    exact reindexIsoOfEq h M
  · intro M N f
    have h' : ∀ p, ((CoordinateShift.translation ε).comp
        (translationNeg (n := n) ε)) p = (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p :=
      h
    change reindexNatTrans ((CoordinateShift.translation ε).comp
        (translationNeg (n := n) ε)) f ≫
          (reindexIsoOfEq (α := (CoordinateShift.translation ε).comp
            (translationNeg (n := n) ε)) (β := OrderHom.id) h' N).hom =
      (reindexIsoOfEq (α := (CoordinateShift.translation ε).comp
        (translationNeg (n := n) ε)) (β := OrderHom.id) h' M).hom ≫
        reindexNatTrans OrderHom.id f
    exact (reindexIsoOfEq_naturality
      (α := (CoordinateShift.translation ε).comp (translationNeg (n := n) ε))
      (β := OrderHom.id) h' f).symm

private def shiftPosNegNatIso (ε : ℝ≥0) :
    shiftNeg (k := k) (n := n) ε ⋙ CoordinateShift.shift ε ≅ 𝟭 _ := by
  let h := translationNegPos_eq_id' (n := n) ε
  refine NatIso.ofComponents (fun M => ?_) ?_
  · change reindex ((translationNeg (n := n) ε).comp
      (CoordinateShift.translation ε)) M ≅ reindex OrderHom.id M
    exact reindexIsoOfEq h M
  · intro M N f
    have h' : ∀ p, ((translationNeg (n := n) ε).comp
        (CoordinateShift.translation ε)) p = (OrderHom.id : (Fin n → ℝ) →o (Fin n → ℝ)) p :=
      h
    change reindexNatTrans ((translationNeg (n := n) ε).comp
        (CoordinateShift.translation ε)) f ≫
          (reindexIsoOfEq (α := (translationNeg (n := n) ε).comp
            (CoordinateShift.translation ε)) (β := OrderHom.id) h' N).hom =
      (reindexIsoOfEq (α := (translationNeg (n := n) ε).comp
        (CoordinateShift.translation ε)) (β := OrderHom.id) h' M).hom ≫
        reindexNatTrans OrderHom.id f
    exact (reindexIsoOfEq_naturality
      (α := (translationNeg (n := n) ε).comp (CoordinateShift.translation ε))
      (β := OrderHom.id) h' f).symm

private def shiftNegPosIso (ε : ℝ≥0) (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    (shiftNeg (k := k) (n := n) ε).obj ((CoordinateShift.shift ε).obj M) ≅ M :=
  (shiftNegPosNatIso (k := k) (n := n) ε).app M

private def shiftPosNegIso (ε : ℝ≥0) (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    (CoordinateShift.shift ε).obj ((shiftNeg (k := k) (n := n) ε).obj M) ≅ M :=
  (shiftPosNegNatIso (k := k) (n := n) ε).app M

@[simp] private theorem shiftNegPosIso_inv_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftNegPosIso (k := k) (n := n) ε M).inv.app p =
      M.map (eqToHom (translationPosNeg_eq_id' (n := n) ε p).symm) := by
  change (reindexIsoOfEq (translationPosNeg_eq_id' (n := n) ε) M).inv.app p = _
  rw [reindexIsoOfEq_inv_app]

@[simp] private theorem shiftNegPosIso_hom_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftNegPosIso (k := k) (n := n) ε M).hom.app p =
      M.map (eqToHom (translationPosNeg_eq_id' (n := n) ε p)) := by
  change (reindexIsoOfEq (translationPosNeg_eq_id' (n := n) ε) M).hom.app p = _
  rw [reindexIsoOfEq_hom_app]

@[simp] private theorem shiftPosNegIso_hom_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftPosNegIso (k := k) (n := n) ε M).hom.app p =
      M.map (eqToHom (translationNegPos_eq_id' (n := n) ε p)) := by
  change (reindexIsoOfEq (translationNegPos_eq_id' (n := n) ε) M).hom.app p = _
  rw [reindexIsoOfEq_hom_app]

@[simp] private theorem shiftPosNegIso_inv_app (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (shiftPosNegIso (k := k) (n := n) ε M).inv.app p =
      M.map (eqToHom (translationNegPos_eq_id' (n := n) ε p).symm) := by
  change (reindexIsoOfEq (translationNegPos_eq_id' (n := n) ε) M).inv.app p = _
  rw [reindexIsoOfEq_inv_app]

private theorem shiftNegPos_inverse_coherence (ε : ℝ≥0)
    (M : PModule.{u,0,u} k (Fin n → ℝ)) :
    (CoordinateShift.shift ε).map (shiftNegPosIso (k := k) (n := n) ε M).inv =
      (shiftPosNegIso (k := k) (n := n) ε
        ((CoordinateShift.shift ε).obj M)).inv := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  ext x
  rw [CoordinateShift.shift_map_app, shiftNegPosIso_inv_app,
    shiftPosNegIso_inv_app]
  change (M.map (eqToHom
      (translationPosNeg_eq_id' (n := n) ε (CoordinateShift.translation ε p)).symm)).hom x =
    (M.map ((CoordinateShift.translation ε).toFunctor.map (eqToHom
      (translationNegPos_eq_id' (n := n) ε p).symm))).hom x
  have hmap := orderFunctor_map_eqToHom (CoordinateShift.translation ε)
    (translationNegPos_eq_id' (n := n) ε p).symm
  have hproof : congrArg (CoordinateShift.translation ε)
      (translationNegPos_eq_id' (n := n) ε p).symm =
      (translationPosNeg_eq_id' (n := n) ε
        (CoordinateShift.translation ε p)).symm := Subsingleton.elim _ _
  have hmaps := hmap.trans (congrArg eqToHom hproof)
  exact congrArg (fun f => f.hom x) (congrArg M.map hmaps)

private theorem shiftNegPosIso_naturality (ε : ℝ≥0)
    {M N : PModule.{u,0,u} k (Fin n → ℝ)} (f : M ⟶ N) :
    (shiftNegPosIso (k := k) (n := n) ε M).hom ≫ f =
      (shiftNeg (k := k) (n := n) ε).map ((CoordinateShift.shift ε).map f) ≫
        (shiftNegPosIso (k := k) (n := n) ε N).hom := by
  change (shiftNegPosNatIso (k := k) (n := n) ε).hom.app M ≫ f =
    (shiftNeg (k := k) (n := n) ε).map
      ((CoordinateShift.shift ε).map f) ≫
      (shiftNegPosNatIso (k := k) (n := n) ε).hom.app N
  exact ((shiftNegPosNatIso (k := k) (n := n) ε).hom.naturality f).symm

private theorem shiftPosNegIso_naturality (ε : ℝ≥0)
    {M N : PModule.{u,0,u} k (Fin n → ℝ)} (f : M ⟶ N) :
    (shiftPosNegIso (k := k) (n := n) ε M).hom ≫ f =
      (CoordinateShift.shift ε).map ((shiftNeg (k := k) (n := n) ε).map f) ≫
        (shiftPosNegIso (k := k) (n := n) ε N).hom := by
  change (shiftPosNegNatIso (k := k) (n := n) ε).hom.app M ≫ f =
    (CoordinateShift.shift ε).map
      ((shiftNeg (k := k) (n := n) ε).map f) ≫
      (shiftPosNegNatIso (k := k) (n := n) ε).hom.app N
  exact ((shiftPosNegNatIso (k := k) (n := n) ε).hom.naturality f).symm

private instance shift_preservesZeroMorphisms (ε : ℝ≥0) :
    (CoordinateShift.shift (R := k) (n := n) ε).PreservesZeroMorphisms where
  map_zero _ _ := by
    apply NatTrans.ext
    funext a
    rfl

private theorem zero_isRankProjective :
    IsRankProjective (0 : PModule.{u,0,u} k (Fin n → ℝ)) := by
  intro L M N ι π hs α
  exact ⟨0, (isZero_zero _).eq_of_src _ _⟩

private theorem zeroTargetRow_rankExact {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (e : M ≅ 0) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0)
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ M) := by
  have hsub (p : Fin n → ℝ) : Subsingleton (M.obj p) := by
    refine ⟨fun x y => ?_⟩
    apply (ModuleCat.mono_iff_injective (e.hom.app p)).mp inferInstance
    exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
  refine {
    toIsPointwiseShortExact := {
      injective := fun p => by
        intro x y _
        letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
        exact Subsingleton.elim _ _
      surjective := fun p y => ⟨0, (hsub p).elim _ _⟩
      range_eq_ker := fun p => by
        letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
          ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
        ext x
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        simp
    }
    finiteDimensional := fun p => by
      letI : Subsingleton ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) :=
        ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)
      letI : Finite ((0 : PModule.{u,0,u} k (Fin n → ℝ)).obj p) := Finite.of_subsingleton
      infer_instance
    rank_add := ?_
  }
  intro a b hab
  have hrange : Subsingleton
      (LinearMap.range (structureMapLinear M hab)) :=
    ⟨fun x y => Subtype.ext ((hsub b).elim x.val y.val)⟩
  letI := hrange
  have hrank : Module.finrank k (LinearMap.range (structureMapLinear M hab)) = 0 :=
    Module.finrank_zero_of_subsingleton
  change rankOfStructureMap (0 : PModule.{u,0,u} k (Fin n → ℝ)) hab =
    rankOfStructureMap (0 : PModule.{u,0,u} k (Fin n → ℝ)) hab +
      rankOfStructureMap M hab
  simp only [rankOfStructureMap_zero]
  change 0 = 0 + Module.finrank k (LinearMap.range (structureMapLinear M hab))
  rw [hrank]

private theorem projectiveIdentityRow
    (P : PModule.{u,0,u} k (Fin n → ℝ))
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) :
    IsRankExact (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ P) (𝟙 P) := by
  letI : ∀ p, FiniteDimensional k (P.obj p) := hfd
  have hs : IsPointwiseShortExact
      (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ P) (𝟙 P) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p x y _
      exact (ModuleCat.subsingleton_of_isZero (Functor.zero_obj p)).elim _ _
    · intro p y
      exact ⟨y, by simp⟩
    · intro p
      ext x
      simp
  exact hs.rankExact_of_section (𝟙 P) (by simp)

/-- The length-one identity resolution of a rank-projective module with
pointwise finite-dimensional fibers. -/
noncomputable def FiniteRankProjectiveResolution.identity
    (P : PModule.{u,0,u} k (Fin n → ℝ)) (hP : IsRankProjective P)
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) :
    FiniteRankProjectiveResolution P := by
  let kernel : Fin 2 → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun _ => P)
  have h0 : kernel (0 : Fin 2) = P := by
    change Fin.lastCases (0 : PModule.{u,0,u} k (Fin n → ℝ))
        (fun _ : Fin 1 => P) ((0 : Fin 1).castSucc) = P
    rw [Fin.lastCases_castSucc]
  have hlast : kernel (Fin.last 1) =
      (0 : PModule.{u,0,u} k (Fin n → ℝ)) := by
    change @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
        (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P) (Fin.last 1) = 0
    rw [Fin.lastCases_last]
  refine {
    toFiniteRankExactResolution := {
      length := 1
      kernel := kernel
      term := fun _ => P
      inclusion := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        change @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
            (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P) (Fin.last 1) ⟶ P
        rw [Fin.lastCases_last]
        exact 0
      quotient := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        change P ⟶ @Fin.lastCases 1 (fun _ : Fin 2 => PModule.{u,0,u} k (Fin n → ℝ))
            (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun _ : Fin 1 => P)
            ((0 : Fin 1).castSucc)
        rw [Fin.lastCases_castSucc]
        exact 𝟙 P
      row_rank_exact := fun i => by
        have hi : i = 0 := by
          apply Fin.ext
          omega
        subst i
        exact projectiveIdentityRow P hfd
      initial_iso := eqToIso h0
      terminal_iso := (eqToIso hlast) ≪≫ Iso.refl _
    }
    term_rank_projective := fun _ => hP
  }

/-- Append one zero projective term to an actual finite resolution.  The old
rows are transported along the canonical finite-index equalities, and the new
last row is rank exact because the old terminal kernel is zero. -/
noncomputable def FiniteRankProjectiveResolution.appendZero
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) : FiniteRankProjectiveResolution M := by
  let kernel : Fin (R.length + 2) → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun i => R.kernel i)
  let term : Fin (R.length + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    Fin.lastCases 0 (fun i => R.term i)
  let hL (i : Fin R.length) : R.kernel i.succ = kernel (i.castSucc).succ := by
    simp only [kernel, Fin.succ_castSucc, Fin.lastCases_castSucc]
  let hM (i : Fin R.length) : R.term i = term i.castSucc := by
    simp only [term, Fin.lastCases_castSucc]
  let hN (i : Fin R.length) : R.kernel i.castSucc = kernel i.castSucc.castSucc := by
    simp only [kernel, Fin.lastCases_castSucc]
  let inclusion : ∀ i, kernel i.succ ⟶ term i := fun i => Fin.lastCases
    (by simp only [kernel, term, Fin.lastCases_last, Fin.succ_last]; exact 0)
    (fun i => (eqToIso (hL i)).inv ≫ R.inclusion i ≫ (eqToIso (hM i)).hom)
    i
  let quotient : ∀ i, term i ⟶ kernel i.castSucc := fun i => Fin.lastCases
    (by
      simpa only [kernel, term, Fin.lastCases_last, Fin.lastCases_castSucc] using
        (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ R.kernel (Fin.last R.length)))
    (fun i => (eqToIso (hM i)).inv ≫ R.quotient i ≫ (eqToIso (hN i)).hom)
    i
  refine {
    toFiniteRankExactResolution := {
      length := R.length + 1
      kernel := kernel
      term := term
      inclusion := inclusion
      quotient := quotient
      row_rank_exact := ?_
      initial_iso := ?_
      terminal_iso := by simpa only [kernel, Fin.lastCases_last] using (Iso.refl 0)
    }
    term_rank_projective := ?_
  }
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · have hL : (0 : PModule.{u,0,u} k (Fin n → ℝ)) =
          kernel (Fin.last R.length).succ := by
        simp only [kernel, Fin.succ_last, Fin.lastCases_last]
      have hM : (0 : PModule.{u,0,u} k (Fin n → ℝ)) =
          term (Fin.last R.length) := by
        simp only [term, Fin.lastCases_last]
      have hN : R.kernel (Fin.last R.length) =
          kernel (Fin.last R.length).castSucc := by
        simp only [kernel, Fin.lastCases_castSucc]
      let eL := eqToIso hL
      let eM := eqToIso hM
      let eN := eqToIso hN
      have hs := (zeroTargetRow_rankExact R.terminal_iso).of_iso eL eM eN
      have hι : inclusion (Fin.last R.length) =
          eL.inv ≫ (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶ 0) ≫ eM.hom := by
        have hsource : IsZero (kernel (Fin.last R.length).succ) :=
          IsZero.of_iso (isZero_zero _) eL.symm
        exact hsource.eq_of_src _ _
      have hπ : quotient (Fin.last R.length) =
          eM.inv ≫ (0 : (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⟶
            R.kernel (Fin.last R.length)) ≫ eN.hom := by
        have hsource : IsZero (term (Fin.last R.length)) :=
          IsZero.of_iso (isZero_zero _) eM.symm
        exact hsource.eq_of_src _ _
      rw [hι, hπ]
      exact hs
    · intro i
      simpa only [inclusion, quotient, Fin.lastCases_castSucc] using
        (R.row_rank_exact i).of_iso (eqToIso (hL i)) (eqToIso (hM i))
          (eqToIso (hN i))
  · have hzero : (0 : Fin (R.length + 2)) = (0 : Fin (R.length + 1)).castSucc := by
      ext
      rfl
    simpa only [kernel, hzero, Fin.lastCases_castSucc] using R.initial_iso
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · have hM : (0 : PModule.{u,0,u} k (Fin n → ℝ)) = term (Fin.last R.length) := by
        simp only [term, Fin.lastCases_last]
      exact zero_isRankProjective.of_iso (eqToIso hM)
    · intro i
      exact (R.term_rank_projective i).of_iso (eqToIso (hM i))

namespace FiniteRankProjectiveResolution

/-- Repeatedly append zero terms, preserving the resolved module and every
existing resolution row. -/
noncomputable def appendZeros {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) :
    (count : ℕ) → FiniteRankProjectiveResolution M
  | 0 => R
  | count + 1 => (appendZeros R count).appendZero

theorem appendZeros_length {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (count : ℕ) :
    (R.appendZeros count).length = R.length + count := by
  induction count with
  | zero => simp [appendZeros]
  | succ count ih =>
      simp [appendZeros, appendZero, ih, Nat.add_assoc]

/-- The degree-`j` term of a finite resolution, extended by zero after its
last indexed projective. -/
noncomputable def termAt {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (j : ℕ) :
    PModule.{u,0,u} k (Fin n → ℝ) :=
  if hj : j < R.length then R.term ⟨j, hj⟩ else 0

@[simp] theorem termAt_eq_term {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) {j : ℕ} (hj : j < R.length) :
    R.termAt j = R.term ⟨j, hj⟩ := by
  simp [termAt, hj]

@[simp] theorem termAt_eq_zero {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) {j : ℕ} (hj : R.length ≤ j) :
    R.termAt j = 0 := by
  simp [termAt, not_lt.mpr hj]

theorem termAt_appendZero {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (j : ℕ) :
    (R.appendZero).termAt j = R.termAt j := by
  by_cases hj : j < R.length
  · have hj' : j < (R.appendZero).length := by
      simp [FiniteRankProjectiveResolution.appendZero]
      omega
    rw [termAt_eq_term (R := R.appendZero) hj', termAt_eq_term (R := R) hj]
    change (Fin.lastCases (0 : PModule.{u,0,u} k (Fin n → ℝ))
      (fun i => R.term i) ⟨j, hj'⟩) = R.term ⟨j, hj⟩
    have hidx : (⟨j, hj'⟩ : Fin (R.length + 1)) = (⟨j, hj⟩ : Fin R.length).castSucc := by
      ext
      rfl
    rw [hidx, Fin.lastCases_castSucc]
  · rw [termAt_eq_zero (R := R) (Nat.le_of_not_gt hj)]
    by_cases hj' : j < (R.appendZero).length
    · have hlast : j = R.length := by
        simp [FiniteRankProjectiveResolution.appendZero] at hj'
        omega
      subst j
      rw [termAt_eq_term (R := R.appendZero) (by
        simp [FiniteRankProjectiveResolution.appendZero])]
      change @Fin.lastCases R.length
          (fun _ : Fin (R.length + 1) => PModule.{u,0,u} k (Fin n → ℝ))
          (0 : PModule.{u,0,u} k (Fin n → ℝ)) (fun i => R.term i)
          (Fin.last R.length) = 0
      simp
    · simp [termAt, hj']

theorem termAt_appendZeros {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (count j : ℕ) :
    (R.appendZeros count).termAt j = R.termAt j := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [appendZeros, termAt_appendZero, ih]

end FiniteRankProjectiveResolution


/-- Remove the first row of a nonempty finite resolution.  The resulting
resolution resolves the actual next kernel; every shifted index is transported
along its explicit finite-index equality. -/
noncomputable def FiniteRankProjectiveResolution.tail
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (hpos : 0 < R.length) :
    FiniteRankProjectiveResolution
      (R.kernel (⟨1, by omega⟩ : Fin (R.length + 1))) := by
  let m : ℕ := R.length - 1
  have hlen : m + 1 = R.length := by dsimp [m]; omega
  let kidx : Fin (m + 1) → Fin (R.length + 1) := fun i =>
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
  let tidx : Fin m → Fin R.length := fun i =>
    ⟨i.val + 1, by have hi := i.isLt; omega⟩
  let kernel : Fin (m + 1) → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun i => R.kernel (kidx i)
  let term : Fin m → PModule.{u,0,u} k (Fin n → ℝ) :=
    fun i => R.term (tidx i)
  have hL (i : Fin m) : R.kernel (tidx i).succ = kernel i.succ := by
    apply congrArg R.kernel
    apply Fin.ext
    rfl
  have hM (i : Fin m) : R.term (tidx i) = term i := rfl
  have hN (i : Fin m) : R.kernel (tidx i).castSucc = kernel i.castSucc := by
    apply congrArg R.kernel
    apply Fin.ext
    rfl
  let inclusion : ∀ i, kernel i.succ ⟶ term i := fun i =>
    (eqToIso (hL i)).inv ≫ R.inclusion (tidx i) ≫ (eqToIso (hM i)).hom
  let quotient : ∀ i, term i ⟶ kernel i.castSucc := fun i =>
    (eqToIso (hM i)).inv ≫ R.quotient (tidx i) ≫ (eqToIso (hN i)).hom
  have h0 : kernel (0 : Fin (m + 1)) =
      R.kernel (⟨1, by omega⟩ : Fin (R.length + 1)) := by
    apply congrArg R.kernel
    apply Fin.ext
    rfl
  have hlast : kernel (Fin.last m) = R.kernel (Fin.last R.length) := by
    apply congrArg R.kernel
    apply Fin.ext
    simp [kidx, hlen]
  refine {
    toFiniteRankExactResolution := {
      length := m
      kernel := kernel
      term := term
      inclusion := inclusion
      quotient := quotient
      row_rank_exact := ?_
      initial_iso := eqToIso h0
      terminal_iso := (eqToIso hlast) ≪≫ R.terminal_iso
    }
    term_rank_projective := ?_
  }
  · intro i
    exact (R.row_rank_exact (tidx i)).of_iso
      (eqToIso (hL i)) (eqToIso (hM i)) (eqToIso (hN i))
  · intro i
    exact (R.term_rank_projective (tidx i)).of_iso (eqToIso (hM i))

@[simp] theorem FiniteRankProjectiveResolution.length_tail
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (hpos : 0 < R.length) :
    (R.tail hpos).length = R.length - 1 := rfl

theorem FiniteRankProjectiveResolution.termAt_tail
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (hpos : 0 < R.length) (j : ℕ) :
    (R.tail hpos).termAt j = R.termAt (j + 1) := by
  by_cases hj : j < R.length - 1
  · have hj' : j < (R.tail hpos).length := by simpa using hj
    have hjR : j + 1 < R.length := by omega
    rw [termAt_eq_term (R := R.tail hpos) hj', termAt_eq_term (R := R) hjR]
    rfl
  · have hj' : (R.tail hpos).length ≤ j := by simpa using Nat.le_of_not_gt hj
    have hjR : R.length ≤ j + 1 := by omega
    rw [termAt_eq_zero (R := R.tail hpos) hj', termAt_eq_zero (R := R) hjR]

/-- Relative projectivity is preserved by coordinate shifts.  This uses that
translation of `Fin n → ℝ` is an order equivalence, so a rank-exact lifting
problem can be transported back along the inverse translation. -/
private theorem IsRankProjective.shift {Q : PModule.{u,0,u} k (Fin n → ℝ)}
    (hQ : IsRankProjective Q) (ε : ℝ≥0) :
    IsRankProjective ((CoordinateShift.shift ε).obj Q) := by
  intro L M N ι π hs α
  let hs' : IsRankExact ((shiftNeg (k := k) (n := n) ε).map ι)
      ((shiftNeg (k := k) (n := n) ε).map π) :=
    hs.reindex (translationNeg (n := n) ε)
  let α' : Q ⟶ (shiftNeg (k := k) (n := n) ε).obj N :=
    (shiftNegPosIso (k := k) (n := n) ε Q).inv ≫
      (shiftNeg (k := k) (n := n) ε).map α
  obtain ⟨β', hβ'⟩ := hQ _ _ _
    ((shiftNeg (k := k) (n := n) ε).map ι)
    ((shiftNeg (k := k) (n := n) ε).map π) hs' α'
  refine ⟨(CoordinateShift.shift ε).map β' ≫
    (shiftPosNegIso (k := k) (n := n) ε M).hom, ?_⟩
  calc
    ((CoordinateShift.shift ε).map β' ≫
          (shiftPosNegIso (k := k) (n := n) ε M).hom) ≫ π =
        (CoordinateShift.shift ε).map β' ≫
          (CoordinateShift.shift ε).map
            ((shiftNeg (k := k) (n := n) ε).map π) ≫
          (shiftPosNegIso (k := k) (n := n) ε N).hom := by
            rw [Category.assoc, shiftPosNegIso_naturality (k := k) (n := n) ε π]
    _ = (CoordinateShift.shift ε).map
          (β' ≫ (shiftNeg (k := k) (n := n) ε).map π) ≫
          (shiftPosNegIso (k := k) (n := n) ε N).hom := by
            exact congrArg (fun f => f ≫ (shiftPosNegIso (k := k) (n := n) ε N).hom)
              ((CoordinateShift.shift ε).map_comp β'
                ((shiftNeg (k := k) (n := n) ε).map π))
    _ = (CoordinateShift.shift ε).map α' ≫
          (shiftPosNegIso (k := k) (n := n) ε N).hom := by rw [hβ']
    _ = α := by
          dsimp [α']
          rw [Functor.map_comp, shiftNegPos_inverse_coherence]
          calc
            ((shiftPosNegIso (k := k) (n := n) ε
                ((CoordinateShift.shift ε).obj Q)).inv ≫
                (CoordinateShift.shift ε).map
                  ((shiftNeg (k := k) (n := n) ε).map α)) ≫
                (shiftPosNegIso (k := k) (n := n) ε N).hom =
                (shiftPosNegIso (k := k) (n := n) ε
                  ((CoordinateShift.shift ε).obj Q)).inv ≫
                  ((CoordinateShift.shift ε).map
                    ((shiftNeg (k := k) (n := n) ε).map α) ≫
                    (shiftPosNegIso (k := k) (n := n) ε N).hom) :=
                  Category.assoc _ _ _
            _ = (shiftPosNegIso (k := k) (n := n) ε
                  ((CoordinateShift.shift ε).obj Q)).inv ≫
                  ((shiftPosNegIso (k := k) (n := n) ε
                    ((CoordinateShift.shift ε).obj Q)).hom ≫ α) := by
                  exact congrArg _
                    (shiftPosNegIso_naturality (k := k) (n := n) ε α).symm
            _ = α := by simp

/-- Shift every object and row of an actual finite rank-projective resolution.
The row witnesses are transported by reindexing, rather than assumed. -/
noncomputable def FiniteRankProjectiveResolution.shift
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (ε : ℝ≥0) :
    FiniteRankProjectiveResolution ((CoordinateShift.shift ε).obj M) where
  toFiniteRankExactResolution := {
    length := R.length
    kernel := fun i => (CoordinateShift.shift ε).obj (R.kernel i)
    term := fun i => (CoordinateShift.shift ε).obj (R.term i)
    inclusion := fun i => (CoordinateShift.shift ε).map (R.inclusion i)
    quotient := fun i => (CoordinateShift.shift ε).map (R.quotient i)
    row_rank_exact := fun i => (R.row_rank_exact i).reindex
      (CoordinateShift.translation ε)
    initial_iso := (CoordinateShift.shift ε).mapIso R.initial_iso
    terminal_iso := (CoordinateShift.shift ε).mapIso R.terminal_iso ≪≫
      Functor.mapZeroObject (CoordinateShift.shift ε)
  }
  term_rank_projective := fun i =>
    (R.term_rank_projective i).shift ε

/-- The selected isomorphism compares each shifted lookup with the shift of the
original lookup, using the corresponding selected zero-object isomorphism beyond
the stored length. -/
noncomputable def FiniteRankProjectiveResolution.termAt_shiftIso
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (ε : ℝ≥0) (j : ℕ) :
    (R.shift ε).termAt j ≅ (CoordinateShift.shift ε).obj (R.termAt j) := by
  by_cases hj : j < R.length
  · have hj' : j < (R.shift ε).length := by
      simpa [FiniteRankProjectiveResolution.shift] using hj
    rw [FiniteRankProjectiveResolution.termAt_eq_term (R := R.shift ε) hj',
      FiniteRankProjectiveResolution.termAt_eq_term (R := R) hj]
    rfl
  · have hle : R.length ≤ j := Nat.le_of_not_gt hj
    have hle' : (R.shift ε).length ≤ j := by
      simpa [FiniteRankProjectiveResolution.shift] using hle
    rw [FiniteRankProjectiveResolution.termAt_eq_zero (R := R.shift ε) hle',
      FiniteRankProjectiveResolution.termAt_eq_zero (R := R) hle]
    exact (Functor.mapZeroObject (CoordinateShift.shift ε)).symm

namespace FiniteRankProjectiveResolution

/-- The zero-padded terms of the selected identity resolution are the module in degree zero and zero thereafter. -/
theorem identity_termAt
    (P : PModule.{u,0,u} k (Fin n → ℝ)) (hP : IsRankProjective P)
    (hfd : ∀ p, FiniteDimensional k (P.obj p)) (j : ℕ) :
    (FiniteRankProjectiveResolution.identity P hP hfd).termAt j =
      if j = 0 then P else 0 := by
  by_cases hj : j = 0
  · subst j
    rw [termAt_eq_term (R := FiniteRankProjectiveResolution.identity P hP hfd) (by
      simp [FiniteRankProjectiveResolution.identity])]
    rfl
  · have hjlen : (FiniteRankProjectiveResolution.identity P hP hfd).length ≤ j := by
      simp [FiniteRankProjectiveResolution.identity]
      omega
    rw [termAt_eq_zero (R := FiniteRankProjectiveResolution.identity P hP hfd) hjlen]
    simp [hj]

end FiniteRankProjectiveResolution

private instance : HasBinaryBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasBinaryBiproducts.of_hasBinaryProducts

private instance : HasFiniteBiproducts (PModule.{u,0,u} k (Fin n → ℝ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private noncomputable def biprodFiberIso
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (A ⊞ B).obj p ≅ ModuleCat.of k (A.obj p × B.obj p) := by
  let F := (evaluation (Fin n → ℝ) (ModuleCat.{u} k)).obj p
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := A) (Y := B)
  exact Functor.mapBiprod F A B ≪≫ ModuleCat.biprodIsoProd (A.obj p) (B.obj p)

private theorem biprodFiberIso_fst
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
      (biprod.fst : A ⊞ B ⟶ A).app p := by
  let F := (evaluation (Fin n → ℝ) (ModuleCat.{u} k)).obj p
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := A) (Y := B)
  let e := ModuleCat.biprodIsoProd (A.obj p) (B.obj p)
  have he : e.hom ≫ ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
      biprod.fst := by
    calc
      e.hom ≫ ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
          e.hom ≫ e.inv ≫ biprod.fst := by
            rw [← ModuleCat.biprodIsoProd_inv_comp_fst]
      _ = biprod.fst := by simp
  calc
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.fst k (A.obj p) (B.obj p)) =
      (Functor.mapBiprod F A B).hom ≫ biprod.fst := by
        dsimp [biprodFiberIso]
        rw [Category.assoc, he]
        rfl
    _ = F.map biprod.fst := by
      change biprod.lift (F.map biprod.fst) (F.map biprod.snd) ≫ biprod.fst = _
      rw [biprod.lift_fst]
    _ = (biprod.fst : A ⊞ B ⟶ A).app p := rfl

private theorem biprodFiberIso_snd
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) (p : Fin n → ℝ) :
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
      (biprod.snd : A ⊞ B ⟶ B).app p := by
  let F := (evaluation (Fin n → ℝ) (ModuleCat.{u} k)).obj p
  letI := preservesBinaryBiproduct_of_preservesBinaryProduct F (X := A) (Y := B)
  let e := ModuleCat.biprodIsoProd (A.obj p) (B.obj p)
  have he : e.hom ≫ ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
      biprod.snd := by
    calc
      e.hom ≫ ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
          e.hom ≫ e.inv ≫ biprod.snd := by
            rw [← ModuleCat.biprodIsoProd_inv_comp_snd]
      _ = biprod.snd := by simp
  calc
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom (LinearMap.snd k (A.obj p) (B.obj p)) =
      (Functor.mapBiprod F A B).hom ≫ biprod.snd := by
        dsimp [biprodFiberIso]
        rw [Category.assoc, he]
        rfl
    _ = F.map biprod.snd := by
      change biprod.lift (F.map biprod.fst) (F.map biprod.snd) ≫ biprod.snd = _
      rw [biprod.lift_snd]
    _ = (biprod.snd : A ⊞ B ⟶ B).app p := rfl

private theorem biprodMap_fiber
    {A B A' B' : PModule.{u,0,u} k (Fin n → ℝ)}
    (f : A ⟶ A') (g : B ⟶ B') (p : Fin n → ℝ) :
    (biprodFiberIso (k := k) (n := n) A B p).hom ≫
        ModuleCat.ofHom ((f.app p).hom.prodMap (g.app p).hom) =
      (biprod.map f g).app p ≫
        (biprodFiberIso (k := k) (n := n) A' B' p).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · have hsrc : ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).1 =
        ((biprod.fst : A ⊞ B ⟶ A).app p).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj p ⟶ A.obj p => q.hom x)
        (biprodFiberIso_fst (k := k) (n := n) A B p)
      simpa [ModuleCat.comp_apply] using h
    have htgt :
        (LinearMap.fst k (A'.obj p) (B'.obj p))
          ((biprodFiberIso (k := k) (n := n) A' B' p).hom.hom
            (((biprod.map f g).app p).hom x)) =
          ((biprod.fst : A' ⊞ B' ⟶ A').app p).hom (((biprod.map f g).app p).hom x) := by
      have h := congrArg (fun q : (A' ⊞ B').obj p ⟶ A'.obj p =>
        q.hom (((biprod.map f g).app p).hom x))
        (biprodFiberIso_fst (k := k) (n := n) A' B' p)
      simpa [ModuleCat.comp_apply] using h
    have hnat : ((biprod.fst : A' ⊞ B' ⟶ A').app p).hom (((biprod.map f g).app p).hom x) =
        (f.app p).hom (((biprod.fst : A ⊞ B ⟶ A).app p).hom x) := by
      have h := congrArg (fun q : A ⊞ B ⟶ A' => (q.app p).hom x)
        (biprod.map_fst (f := f) (g := g))
      exact h
    calc
      _ = (f.app p).hom (((biprod.fst : A ⊞ B ⟶ A).app p).hom x) := by
        change (f.app p).hom ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).1 = _
        rw [hsrc]
      _ = ((biprod.fst : A' ⊞ B' ⟶ A').app p).hom (((biprod.map f g).app p).hom x) := hnat.symm
      _ = _ := htgt.symm

  · have hsrc : ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).2 =
        ((biprod.snd : A ⊞ B ⟶ B).app p).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj p ⟶ B.obj p => q.hom x)
        (biprodFiberIso_snd (k := k) (n := n) A B p)
      simpa [ModuleCat.comp_apply] using h
    have htgt :
        (LinearMap.snd k (A'.obj p) (B'.obj p))
          ((biprodFiberIso (k := k) (n := n) A' B' p).hom.hom
            (((biprod.map f g).app p).hom x)) =
          ((biprod.snd : A' ⊞ B' ⟶ B').app p).hom (((biprod.map f g).app p).hom x) := by
      have h := congrArg (fun q : (A' ⊞ B').obj p ⟶ B'.obj p =>
        q.hom (((biprod.map f g).app p).hom x))
        (biprodFiberIso_snd (k := k) (n := n) A' B' p)
      simpa [ModuleCat.comp_apply] using h
    have hnat : ((biprod.snd : A' ⊞ B' ⟶ B').app p).hom (((biprod.map f g).app p).hom x) =
        (g.app p).hom (((biprod.snd : A ⊞ B ⟶ B).app p).hom x) := by
      have h := congrArg (fun q : A ⊞ B ⟶ B' => (q.app p).hom x)
        (biprod.map_snd (f := f) (g := g))
      exact h
    calc
      _ = (g.app p).hom (((biprod.snd : A ⊞ B ⟶ B).app p).hom x) := by
        change (g.app p).hom ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x).2 = _
        rw [hsrc]
      _ = ((biprod.snd : A' ⊞ B' ⟶ B').app p).hom (((biprod.map f g).app p).hom x) := hnat.symm
      _ = _ := htgt.symm


private theorem biprodMap_fiber_apply
    {A B A' B' : PModule.{u,0,u} k (Fin n → ℝ)}
    (f : A ⟶ A') (g : B ⟶ B') (p : Fin n → ℝ)
    (x : (A ⊞ B).obj p) :
    ((biprodFiberIso (k := k) (n := n) A' B' p).hom.hom
      (((biprod.map f g).app p).hom x)) =
      (f.app p).hom.prodMap (g.app p).hom
        ((biprodFiberIso (k := k) (n := n) A B p).hom.hom x) := by
  have h := congrArg (fun q : (A ⊞ B).obj p ⟶
      ModuleCat.of k (A'.obj p × B'.obj p) => q.hom x)
    (biprodMap_fiber (k := k) (n := n) f g p)
  simpa [ModuleCat.comp_apply] using h.symm

private theorem biprodStructureMap_fiber
    (A B : PModule.{u,0,u} k (Fin n → ℝ)) {a b : Fin n → ℝ}
    (hab : a ≤ b) (x : (A ⊞ B).obj a) :
    ((biprodFiberIso (k := k) (n := n) A B b).hom.hom
      (structureMapLinear (A ⊞ B) hab x)) =
      (structureMapLinear A hab).prodMap (structureMapLinear B hab)
        ((biprodFiberIso (k := k) (n := n) A B a).hom.hom x) := by
  let ea := biprodFiberIso (k := k) (n := n) A B a
  let eb := biprodFiberIso (k := k) (n := n) A B b
  apply Prod.ext
  · have hsrc : (ea.hom.hom x).1 =
        ((biprod.fst : A ⊞ B ⟶ A).app a).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj a ⟶ A.obj a => q.hom x)
        (biprodFiberIso_fst (k := k) (n := n) A B a)
      simpa [ModuleCat.comp_apply] using h
    have htgt : (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).1 =
        ((biprod.fst : A ⊞ B ⟶ A).app b).hom (structureMapLinear (A ⊞ B) hab x) := by
      have h := congrArg (fun q : (A ⊞ B).obj b ⟶ A.obj b =>
        q.hom (structureMapLinear (A ⊞ B) hab x))
        (biprodFiberIso_fst (k := k) (n := n) A B b)
      simpa [ModuleCat.comp_apply] using h
    have hnat := congrArg (fun q : (A ⊞ B).obj a ⟶ A.obj b => q.hom x)
      ((biprod.fst : A ⊞ B ⟶ A).naturality (homOfLE hab))
    change ((biprod.fst : A ⊞ B ⟶ A).app b).hom
        (structureMapLinear (A ⊞ B) hab x) =
      (structureMapLinear A hab)
        (((biprod.fst : A ⊞ B ⟶ A).app a).hom x) at hnat
    calc
      (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).1 =
          ((biprod.fst : A ⊞ B ⟶ A).app b).hom
            (structureMapLinear (A ⊞ B) hab x) := htgt
      _ = (structureMapLinear A hab)
          (((biprod.fst : A ⊞ B ⟶ A).app a).hom x) := hnat
      _ = (structureMapLinear A hab) ((ea.hom.hom x).1) := by rw [hsrc]
      _ = ((structureMapLinear A hab).prodMap (structureMapLinear B hab)
          (ea.hom.hom x)).1 := rfl
  · have hsrc : (ea.hom.hom x).2 =
        ((biprod.snd : A ⊞ B ⟶ B).app a).hom x := by
      have h := congrArg (fun q : (A ⊞ B).obj a ⟶ B.obj a => q.hom x)
        (biprodFiberIso_snd (k := k) (n := n) A B a)
      simpa [ModuleCat.comp_apply] using h
    have htgt : (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).2 =
        ((biprod.snd : A ⊞ B ⟶ B).app b).hom (structureMapLinear (A ⊞ B) hab x) := by
      have h := congrArg (fun q : (A ⊞ B).obj b ⟶ B.obj b =>
        q.hom (structureMapLinear (A ⊞ B) hab x))
        (biprodFiberIso_snd (k := k) (n := n) A B b)
      simpa [ModuleCat.comp_apply] using h
    have hnat := congrArg (fun q : (A ⊞ B).obj a ⟶ B.obj b => q.hom x)
      ((biprod.snd : A ⊞ B ⟶ B).naturality (homOfLE hab))
    change ((biprod.snd : A ⊞ B ⟶ B).app b).hom
        (structureMapLinear (A ⊞ B) hab x) =
      (structureMapLinear B hab)
        (((biprod.snd : A ⊞ B ⟶ B).app a).hom x) at hnat
    calc
      (eb.hom.hom (structureMapLinear (A ⊞ B) hab x)).2 =
          ((biprod.snd : A ⊞ B ⟶ B).app b).hom
            (structureMapLinear (A ⊞ B) hab x) := htgt
      _ = (structureMapLinear B hab)
          (((biprod.snd : A ⊞ B ⟶ B).app a).hom x) := hnat
      _ = (structureMapLinear B hab) ((ea.hom.hom x).2) := by rw [hsrc]
      _ = ((structureMapLinear A hab).prodMap (structureMapLinear B hab)
          (ea.hom.hom x)).2 := rfl

namespace IsPointwiseShortExact

/-- Pointwise short exactness is preserved by binary biproducts.  The proof
identifies each evaluated biproduct with the product of its two fibers and
checks exactness in the two coordinates. -/
private theorem biprod
    {A A' A'' B B' B'' : PModule.{u,0,u} k (Fin n → ℝ)}
    {f : A ⟶ A'} {g : A' ⟶ A''} {f' : B ⟶ B'} {g' : B' ⟶ B''}
    (hA : IsPointwiseShortExact f g) (hB : IsPointwiseShortExact f' g') :
    IsPointwiseShortExact (biprod.map f f') (biprod.map g g') where
  injective p := by
    let e₀ := biprodFiberIso (k := k) (n := n) A B p
    let e₁ := biprodFiberIso (k := k) (n := n) A' B' p
    intro x y h
    apply (ModuleCat.mono_iff_injective e₀.hom).mp inferInstance
    apply Prod.ext
    · have hx := biprodMap_fiber_apply (k := k) (n := n) f f' p x
      have hy := biprodMap_fiber_apply (k := k) (n := n) f f' p y
      have heq := congrArg e₁.hom.hom h
      have hc : (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom x) =
          (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom y) := by
        rw [← hx, ← hy]
        exact heq
      exact hA.injective p (congrArg Prod.fst hc)
    · have hx := biprodMap_fiber_apply (k := k) (n := n) f f' p x
      have hy := biprodMap_fiber_apply (k := k) (n := n) f f' p y
      have heq := congrArg e₁.hom.hom h
      have hc : (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom x) =
          (f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom y) := by
        rw [← hx, ← hy]
        exact heq
      exact hB.injective p (congrArg Prod.snd hc)
  surjective p := by
    let e₀ := biprodFiberIso (k := k) (n := n) A B p
    let e₁ := biprodFiberIso (k := k) (n := n) A' B' p
    let e₂ := biprodFiberIso (k := k) (n := n) A'' B'' p
    intro z
    obtain ⟨x, hx⟩ := hA.surjective p (e₂.hom.hom z).1
    obtain ⟨y, hy⟩ := hB.surjective p (e₂.hom.hom z).2
    refine ⟨e₁.inv.hom (x, y), ?_⟩
    apply (ModuleCat.mono_iff_injective e₂.hom).mp inferInstance
    calc
      e₂.hom.hom (((biprod.map g g').app p).hom (e₁.inv.hom (x, y))) =
          (g.app p).hom.prodMap (g'.app p).hom
            (e₁.hom.hom (e₁.inv.hom (x, y))) :=
        biprodMap_fiber_apply (k := k) (n := n) g g' p _
      _ = e₂.hom.hom z := by simp [hx, hy]
  range_eq_ker p := by
    let e₀ := biprodFiberIso (k := k) (n := n) A B p
    let e₁ := biprodFiberIso (k := k) (n := n) A' B' p
    let e₂ := biprodFiberIso (k := k) (n := n) A'' B'' p
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      apply (ModuleCat.mono_iff_injective e₂.hom).mp inferInstance
      change (e₂.hom.hom (((biprod.map g g').app p).hom
          (((biprod.map f f').app p).hom x))) = e₂.hom.hom 0
      calc
        e₂.hom.hom (((biprod.map g g').app p).hom
            (((biprod.map f f').app p).hom x)) =
            (g.app p).hom.prodMap (g'.app p).hom
              (e₁.hom.hom (((biprod.map f f').app p).hom x)) :=
          biprodMap_fiber_apply (k := k) (n := n) g g' p _
        _ = (g.app p).hom.prodMap (g'.app p).hom
            ((f.app p).hom.prodMap (f'.app p).hom (e₀.hom.hom x)) := by
          rw [biprodMap_fiber_apply (k := k) (n := n) f f' p x]
        _ = 0 := by
          apply Prod.ext
          · have hmem : (f.app p).hom (e₀.hom.hom x).1 ∈
                LinearMap.range (f.app p).hom := ⟨(e₀.hom.hom x).1, rfl⟩
            rw [hA.range_eq_ker p] at hmem
            exact LinearMap.mem_ker.mp hmem
          · have hmem : (f'.app p).hom (e₀.hom.hom x).2 ∈
                LinearMap.range (f'.app p).hom := ⟨(e₀.hom.hom x).2, rfl⟩
            rw [hB.range_eq_ker p] at hmem
            exact LinearMap.mem_ker.mp hmem
        _ = e₂.hom.hom 0 := by simp
    · intro hz
      change ((biprod.map g g').app p).hom z = 0 at hz
      have hz' : (g.app p).hom.prodMap (g'.app p).hom (e₁.hom.hom z) = 0 := by
        rw [← biprodMap_fiber_apply (k := k) (n := n) g g' p z]
        simp [hz]
      have hxker : (e₁.hom.hom z).1 ∈ LinearMap.ker (g.app p).hom :=
        LinearMap.mem_ker.mpr (by simpa using congrArg Prod.fst hz')
      have hyker : (e₁.hom.hom z).2 ∈ LinearMap.ker (g'.app p).hom :=
        LinearMap.mem_ker.mpr (by simpa using congrArg Prod.snd hz')
      rw [← hA.range_eq_ker p] at hxker
      rw [← hB.range_eq_ker p] at hyker
      obtain ⟨x, hx⟩ := hxker
      obtain ⟨y, hy⟩ := hyker
      refine ⟨e₀.inv.hom (x, y), ?_⟩
      apply (ModuleCat.mono_iff_injective e₁.hom).mp inferInstance
      calc
        e₁.hom.hom (((biprod.map f f').app p).hom (e₀.inv.hom (x, y))) =
            (f.app p).hom.prodMap (f'.app p).hom
              (e₀.hom.hom (e₀.inv.hom (x, y))) :=
          biprodMap_fiber_apply (k := k) (n := n) f f' p _
        _ = e₁.hom.hom z := by simp [hx, hy]

end IsPointwiseShortExact

namespace IsRankExact

/-- Binary biproducts preserve rank exactness.  The lifting criterion is
applied coordinatewise through the evaluated biproduct/product isomorphisms. -/
private theorem biprod
    {A A' A'' B B' B'' : PModule.{u,0,u} k (Fin n → ℝ)}
    {f : A ⟶ A'} {g : A' ⟶ A''} {f' : B ⟶ B'} {g' : B' ⟶ B''}
    (hA : IsRankExact f g) (hB : IsRankExact f' g') :
    IsRankExact (biprod.map f f') (biprod.map g g') := by
  let hshort := hA.toIsPointwiseShortExact.biprod hB.toIsPointwiseShortExact
  refine {
    toIsPointwiseShortExact := hshort
    finiteDimensional := ?_
    rank_add := ?_
  }
  · intro p
    let e := biprodFiberIso (k := k) (n := n) A' B' p
    letI : FiniteDimensional k (A'.obj p) := hA.finiteDimensional p
    letI : FiniteDimensional k (B'.obj p) := hB.finiteDimensional p
    letI : FiniteDimensional k (A'.obj p × B'.obj p) := inferInstance
    have hsurj : Function.Surjective e.inv.hom := by
      intro x
      exact ⟨e.hom.hom x, by simp⟩
    exact FiniteDimensional.of_surjective e.inv.hom hsurj
  · intro a b hab
    let hmidA := biprodFiberIso (k := k) (n := n) A' B' a
    let hmidB := biprodFiberIso (k := k) (n := n) A' B' b
    let hquotA := biprodFiberIso (k := k) (n := n) A'' B'' a
    letI : FiniteDimensional k (A'.obj a) := hA.finiteDimensional a
    letI : FiniteDimensional k (B'.obj a) := hB.finiteDimensional a
    letI : FiniteDimensional k (A'.obj a × B'.obj a) := inferInstance
    have hsurj : Function.Surjective hmidA.inv.hom := by
      intro x
      exact ⟨hmidA.hom.hom x, by simp⟩
    letI : FiniteDimensional k ((A' ⊞ B').obj a) :=
      FiniteDimensional.of_surjective hmidA.inv.hom hsurj
    apply (hshort.rank_add_iff_lift_kernel hab).mpr
    intro z hz
    have hzpair : (structureMapLinear A'' hab).prodMap
        (structureMapLinear B'' hab) (hquotA.hom.hom z) = 0 := by
      rw [← biprodStructureMap_fiber (k := k) (n := n) A'' B'' hab z]
      simp [hz]
    have hza : structureMapLinear A'' hab (hquotA.hom.hom z).1 = 0 := by
      simpa using congrArg Prod.fst hzpair
    have hzb : structureMapLinear B'' hab (hquotA.hom.hom z).2 = 0 := by
      simpa using congrArg Prod.snd hzpair
    obtain ⟨x, hx, hxdie⟩ := hA.lift_kernel hab (hquotA.hom.hom z).1 hza
    obtain ⟨y, hy, hydie⟩ := hB.lift_kernel hab (hquotA.hom.hom z).2 hzb
    let w := hmidA.inv.hom (x, y)
    refine ⟨w, ?_, ?_⟩
    · apply (ModuleCat.mono_iff_injective hquotA.hom).mp inferInstance
      calc
        hquotA.hom.hom (((biprod.map g g').app a).hom w) =
            (g.app a).hom.prodMap (g'.app a).hom
              (hmidA.hom.hom w) :=
          biprodMap_fiber_apply (k := k) (n := n) g g' a w
        _ = hquotA.hom.hom z := by simp [w, hx, hy]
    · apply (ModuleCat.mono_iff_injective hmidB.hom).mp inferInstance
      rw [biprodStructureMap_fiber (k := k) (n := n) A' B' hab w]
      have hw : hmidA.hom.hom w = (x, y) := by
        change hmidA.hom.hom (hmidA.inv.hom (x, y)) = (x, y)
        have h := congrArg (fun q : ModuleCat.of k (A'.obj a × B'.obj a) ⟶
            ModuleCat.of k (A'.obj a × B'.obj a) => q.hom (x, y))
          hmidA.inv_hom_id
        simpa [ModuleCat.comp_apply] using h
      rw [hw]
      have hpair : (structureMapLinear A' hab).prodMap
          (structureMapLinear B' hab) (x, y) = 0 := Prod.ext hxdie hydie
      simpa using hpair

end IsRankExact

namespace IsRankProjective

/-- The binary biproduct of two rank-projectives is rank-projective. -/
private theorem biprod {P Q : PModule.{u,0,u} k (Fin n → ℝ)}
    (hP : IsRankProjective P) (hQ : IsRankProjective Q) :
    IsRankProjective (P ⊞ Q) := by
  intro L M N ι π hs α
  obtain ⟨βP, hβP⟩ := hP L M N ι π hs (biprod.inl ≫ α)
  obtain ⟨βQ, hβQ⟩ := hQ L M N ι π hs (biprod.inr ≫ α)
  refine ⟨biprod.desc βP βQ, ?_⟩
  apply biprod.hom_ext'
  · simpa only [← Category.assoc, biprod.inl_desc] using hβP
  · simpa only [← Category.assoc, biprod.inr_desc] using hβQ

end IsRankProjective

private theorem isZeroZeroBiprod :
    IsZero ((0 : PModule.{u,0,u} k (Fin n → ℝ)) ⊞ 0) := by
  refine ⟨?_, ?_⟩
  · intro Y
    refine ⟨{ default := (0 : (0 ⊞ 0) ⟶ Y), uniq := ?_ }⟩
    intro f
    apply biprod.hom_ext'
    · exact (isZero_zero _).eq_of_src
        (biprod.inl ≫ f) 0
    · exact (isZero_zero _).eq_of_src
        (biprod.inr ≫ f) 0
  · intro Y
    refine ⟨{ default := (0 : Y ⟶ (0 ⊞ 0)), uniq := ?_ }⟩
    intro f
    apply biprod.hom_ext
    · exact (isZero_zero _).eq_of_tgt
        (f ≫ biprod.fst) (0 ≫ biprod.fst)
    · exact (isZero_zero _).eq_of_tgt
        (f ≫ biprod.snd) (0 ≫ biprod.snd)

private noncomputable def zeroBiprodIso :
    (0 : PModule.{u,0,u} k (Fin n → ℝ)) ⊞ 0 ≅
      (0 : PModule.{u,0,u} k (Fin n → ℝ)) :=
  isZeroZeroBiprod.iso (isZero_zero _)

namespace FiniteRankProjectiveResolution

/-- A binary biproduct of two finite rank-projective resolutions of the same
length is again an actual finite rank-projective resolution. -/
noncomputable def biprod {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) :
    FiniteRankProjectiveResolution (M ⊞ N) where
  toFiniteRankExactResolution := {
    length := R.length
    kernel := fun i => R.kernel i ⊞ S.kernel (Fin.cast (congrArg Nat.succ hlen) i)
    term := fun i => R.term i ⊞ S.term (Fin.cast hlen i)
    inclusion := fun i => biprod.map (R.inclusion i)
      (S.inclusion (Fin.cast hlen i))
    quotient := fun i => biprod.map (R.quotient i)
      (S.quotient (Fin.cast hlen i))
    row_rank_exact := fun i => (R.row_rank_exact i).biprod
      (S.row_rank_exact (Fin.cast hlen i))
    initial_iso := biprod.mapIso R.initial_iso S.initial_iso
    terminal_iso :=
      (biprod.mapIso R.terminal_iso
        ((eqToIso (by
          congr 1
          apply Fin.ext
          simp)).trans S.terminal_iso)) ≪≫ zeroBiprodIso
  }
  term_rank_projective := fun i =>
    (R.term_rank_projective i).biprod
      (S.term_rank_projective (Fin.cast hlen i))

end FiniteRankProjectiveResolution

namespace FiniteRankProjectiveResolution

/-- The selected lookup for a binary biproduct resolution identifies its
zero-padded term at `j` with the biproduct of the two selected zero-padded
terms at `j`. At or beyond the common stored length it uses the chosen
zero-biproduct isomorphism. -/
noncomputable def termAt_biprodIso
    {M N : PModule.{u,0,u} k (Fin n → ℝ)}
    (R : FiniteRankProjectiveResolution M) (S : FiniteRankProjectiveResolution N)
    (hlen : R.length = S.length) (j : ℕ) :
    (R.biprod S hlen).termAt j ≅ R.termAt j ⊞ S.termAt j := by
  by_cases hj : j < R.length
  · have hjS : j < S.length := by omega
    rw [termAt_eq_term (R := R.biprod S hlen) hj,
      termAt_eq_term (R := R) hj, termAt_eq_term (R := S) hjS]
    change (R.term ⟨j, hj⟩ ⊞ S.term (Fin.cast hlen ⟨j, hj⟩)) ≅
      R.term ⟨j, hj⟩ ⊞ S.term ⟨j, hjS⟩
    have hidx : Fin.cast hlen (⟨j, hj⟩ : Fin R.length) = ⟨j, hjS⟩ := by
      apply Fin.ext
      rfl
    exact biprod.mapIso (Iso.refl _) (eqToIso (congrArg S.term hidx))
  · have hjS : S.length ≤ j := by omega
    rw [termAt_eq_zero (R := R.biprod S hlen) (by simpa [FiniteRankProjectiveResolution.biprod] using Nat.le_of_not_gt hj),
      termAt_eq_zero (R := R) (Nat.le_of_not_gt hj),
      termAt_eq_zero (R := S) hjS]
    exact (zeroBiprodIso (k := k) (n := n)).symm

end FiniteRankProjectiveResolution

end RealCoordinateOperations

end TDA.Persistence
