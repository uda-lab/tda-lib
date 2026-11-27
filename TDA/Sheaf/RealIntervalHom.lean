import TDA.Sheaf.RealConstructibleRefinement
import TDA.Sheaf.AlternatingReflection

/-!
# Morphisms on the strata of the real line

The value of a morphism of interval diagrams at any common vertex determines it.
A morphism with prescribed value exists if each arrow from a source point to
a target cell has either both endpoints in the overlap or neither endpoint in the overlap.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite TDA.Persistence
open TDA.Sheaf.AlternatingDiagram TDA.Sheaf.RealStratification

namespace TDA.Sheaf.RealConstructible

variable (k : Type) [Field k] {m : ℕ} {p : Fin m → ℝ}

local notation "V" => Fin (2 * m + 1)
local notation "D[" J "]" => interval (k := k) (orient m) J
local notation "ISh[" hp "," J "]" => Functor.obj (extension k hp) D[J]

variable {J K : FiniteInterval (2 * m + 1)}

local notation "unitAt[" j "," v "]" => unitVec (k := k) (o := orient m) j v

private theorem fiber_eq_smul_one {J : FiniteInterval (2 * m + 1)} {v : V}
    (hv : J.alive v) (x : D[J].obj (vtx (orient m) v)) :
    x = ival x • unitAt[J,v] :=
  ival_injective (by simp [ival_unitVec, hv])

private theorem intervalMap_gen_apply_val {v w : V} (h : Arrow (orient m) v w)
    (x : D[J].obj (vtx (orient m) v)) :
    ival (D[J].map (gen h) x) = if J.alive v ∧ J.alive w then ival x else 0 := by
  simpa only [arr_of_arrow _ h, h, true_and] using arr_interval_val J v w x

private def diagramScalar (f : D[J] ⟶ D[K]) (v : V) : k :=
  ival (f.app (vtx (orient m) v) (unitAt[J,v]))

private theorem diagramScalar_eq_of_arrow (f : D[J] ⟶ D[K]) {v w : V}
    (h : Arrow (orient m) v w) (hv : J.alive v) (hw : J.alive w)
    (hv' : K.alive v) (hw' : K.alive w) :
    diagramScalar k f v = diagramScalar k f w := by
  have hm : D[J].map (gen h) (unitAt[J,v]) = unitAt[J,w] :=
    ival_injective (by rw [intervalMap_gen_apply_val k h]; simp [hv, hw, ival_unitVec])
  have hn := ConcreteCategory.congr_hom (f.naturality (gen h)) (unitAt[J,v])
  change f.app (vtx (orient m) w) (D[J].map (gen h) (unitAt[J,v])) =
    D[K].map (gen h) (f.app (vtx (orient m) v) (unitAt[J,v])) at hn
  rw [hm] at hn
  have he := congrArg (ival (J := K) (l := w)) hn
  rw [intervalMap_gen_apply_val k h, ite_eq_left ⟨hv', hw'⟩] at he
  exact he.symm

private theorem diagramScalar_eq (f : D[J] ⟶ D[K]) {v w : V}
    (hv : J.alive v) (hw : J.alive w) (hv' : K.alive v) (hw' : K.alive w) :
    diagramScalar k f v = diagramScalar k f w := by
  suffices ordered : ∀ {v w : V}, v ≤ w → J.alive v → J.alive w →
      K.alive v → K.alive w → diagramScalar k f v = diagramScalar k f w by
    exact (le_total v w).elim (fun h => ordered h hv hw hv' hw')
      (fun h => (ordered h hw hv hw' hv').symm)
  intro v w hvw hv hw hv' hw'
  have chain : ∀ t (ht : v.val ≤ t) (htw : t ≤ w.val),
      diagramScalar k f v = diagramScalar k f ⟨t, htw.trans_lt w.isLt⟩ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro; rfl
    | succ t ht ih =>
      intro ht'
      let a : V := ⟨t, by omega⟩
      let b : V := ⟨t + 1, ht'.trans_lt w.isLt⟩
      have ha : J.alive a := ⟨hv.1.trans ht, (Nat.le_succ t).trans_lt (ht'.trans_lt hw.2)⟩
      have hb : J.alive b := ⟨hv.1.trans (ht.trans (Nat.le_succ t)), ht'.trans_lt hw.2⟩
      have ha' : K.alive a := ⟨hv'.1.trans ht, (Nat.le_succ t).trans_lt (ht'.trans_lt hw'.2)⟩
      have hb' : K.alive b := ⟨hv'.1.trans (ht.trans (Nat.le_succ t)), ht'.trans_lt hw'.2⟩
      refine (ih (by omega)).trans ?_
      rcases arrow_or_arrow (orient m) (i := a) (j := b) (Or.inl rfl) with h | h
      · exact diagramScalar_eq_of_arrow k f h ha hb ha' hb'
      · exact (diagramScalar_eq_of_arrow k f h hb ha hb' ha').symm
  exact chain w.val hvw le_rfl

private theorem diagramEval_injective {v : V} (hv : J.alive v) (hv' : K.alive v) :
    Function.Injective (fun f : D[J] ⟶ D[K] => f.app (vtx (orient m) v)) := by
  intro f g hfg
  apply NatTrans.ext
  funext w
  change f.app (vtx (orient m) w) = g.app (vtx (orient m) w)
  ext x : 2
  change f.app (vtx (orient m) w) x = g.app (vtx (orient m) w) x
  by_cases hw : J.alive w
  · by_cases hw' : K.alive w
    · have hscalar : diagramScalar k f w = diagramScalar k g w := calc
        _ = diagramScalar k f v := diagramScalar_eq k f hw hv hw' hv'
        _ = diagramScalar k g v := by simp only [diagramScalar, hfg]
        _ = _ := diagramScalar_eq k g hv hw hv' hw'
      have hone : f.app (vtx (orient m) w) (unitAt[J,w]) =
          g.app (vtx (orient m) w) (unitAt[J,w]) := ival_injective hscalar
      conv_lhs => rw [fiber_eq_smul_one k hw x]
      conv_rhs => rw [fiber_eq_smul_one k hw x]
      rw [map_smul, map_smul, hone]
    · exact ival_injective ((ival_eq_zero hw' _).trans (ival_eq_zero hw' _).symm)
  · have hx : x = 0 := ival_injective (ival_eq_zero hw x)
    rw [hx, map_zero, map_zero]

private def scalarComponent (c : k) (v : V) :
    D[J].obj (vtx (orient m) v) →ₗ[k] D[K].obj (vtx (orient m) v) :=
  show J.fiber (k := k) v →ₗ[k] K.fiber (k := k) v from
  if hv : J.alive v ∧ K.alive v then
    c • Submodule.inclusion (by simp [FiniteInterval.fiber, hv.1, hv.2])
  else 0

private theorem scalarComponent_val (c : k) (v : V) (x : D[J].obj (vtx (orient m) v)) :
    ival (J := K) (o := orient m) (l := v) (scalarComponent k c v x) =
      if J.alive v ∧ K.alive v then c * ival (J := J) (o := orient m) (l := v) x else 0 := by
  by_cases h : J.alive v ∧ K.alive v
  · rw [ite_eq_left h]
    simp only [scalarComponent, dite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    simp only [scalarComponent, dite_eq_right h]
    rfl

private def diagramHomOfScalar
    (harrow : ∀ ⦃v w : V⦄, Arrow (orient m) v w →
      J.alive v → K.alive w → (J.alive w ↔ K.alive v)) (c : k) : D[J] ⟶ D[K] :=
  homMk (fun v => ModuleCat.ofHom (scalarComponent k c v)) (by
    intro v w h
    ext x : 2
    apply Subtype.ext
    change ival (J := K) (o := orient m) (l := w)
        (scalarComponent k c w (D[J].map (gen h) x)) =
      ival (D[K].map (gen h) (scalarComponent (K := K) k c v x))
    rw [scalarComponent_val, intervalMap_gen_apply_val k h, intervalMap_gen_apply_val k h,
      scalarComponent_val]
    by_cases hv : J.alive v <;> by_cases hw : K.alive w
    · by_cases hJw : J.alive w
      · have hKv := (harrow h hv hw).1 hJw
        simp [hv, hw, hJw, hKv]
      · have hKv := mt (harrow h hv hw).2 hJw
        simp [hJw, hKv]
    · simp [hw]
    · by_cases hJw : J.alive w <;> simp [hv, hJw]
    · simp [hw])

private theorem diagramEval_surjective {v : V} (hv : J.alive v) (hv' : K.alive v)
    (harrow : ∀ ⦃v w : V⦄, Arrow (orient m) v w →
      J.alive v → K.alive w → (J.alive w ↔ K.alive v)) :
    Function.Surjective (fun f : D[J] ⟶ D[K] => f.app (vtx (orient m) v)) := by
  intro g
  let c : k := ival (g (unitAt[J,v]))
  refine ⟨diagramHomOfScalar k harrow c, ?_⟩
  ext x : 2
  apply Subtype.ext
  change ival (J := K) (o := orient m) (l := v) (scalarComponent k c v x) = ival (g x)
  rw [scalarComponent_val, ite_eq_left ⟨hv, hv'⟩]
  conv_rhs => rw [fiber_eq_smul_one k hv x]
  rw [map_smul, ival_smul]
  exact mul_comm _ _

/-- Evaluation on a common stalk is bijective if the arrow equations allow a
common scalar. For an arrow from a source point to a target cell, the endpoints
must either both lie in the overlap or both lie outside it. -/
theorem bijective_stalkMap_interval_of_arrows (hp : StrictMono p)
    {x : ℝ} {v : V} (hx : x ∈ stratum p v) (hv : J.alive v) (hv' : K.alive v)
    (harrow : ∀ ⦃u w : V⦄, Arrow (orient m) u w →
      J.alive u → K.alive w → (J.alive w ↔ K.alive u)) :
    Function.Bijective (fun f : ISh[hp,J] ⟶ ISh[hp,K] =>
      (TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) x).map f.hom) := by
  let U := star p v
  let hxU := stratum_subset_star v hx
  let germ (L : FiniteInterval (2 * m + 1)) := ISh[hp,L].presheaf.germ U x hxU
  have hg (L : FiniteInterval (2 * m + 1)) : IsIso (germ L) :=
    isIso_germ_star_of_mem_stratum hp
      (isConstructible_extension k hp (M := D[L]) fun _ => inferInstance) hx
  let e (L : FiniteInterval (2 * m + 1)) :=
    (asIso (germ L)).symm ≪≫ extensionStarIso k hp D[L] v
  let st := TopCat.Presheaf.stalkFunctor (ModuleCat k) (X := realLine) x
  let Φ := extension k hp
  have he (f : D[J] ⟶ D[K]) :
      (e J).homCongr (e K) (st.map (Φ.map f).hom) = f.app (vtx (orient m) v) := by
    have hn := congrArg (fun η => η.app (vtx (orient m) v))
      ((extensionSectionsIso k hp).inv.naturality f)
    change f.app (vtx (orient m) v) ≫ (extensionStarIso k hp D[K] v).inv =
      (extensionStarIso k hp D[J] v).inv ≫ (Φ.map f).hom.app (op U) at hn
    apply (cancel_mono (e K).inv).mp
    change ((extensionStarIso k hp D[J] v).inv ≫ germ J) ≫
        (st.map (Φ.map f).hom ≫ (e K).hom) ≫ (e K).inv =
      f.app (vtx (orient m) v) ≫ (extensionStarIso k hp D[K] v).inv ≫ germ K
    calc
      _ = (extensionStarIso k hp D[J] v).inv ≫ (Φ.map f).hom.app (op U) ≫ germ K := by
        have hcancel : (st.map (Φ.map f).hom ≫ (e K).hom) ≫ (e K).inv =
            st.map (Φ.map f).hom := by
          erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        erw [Category.assoc, hcancel]
        exact congrArg ((extensionStarIso k hp D[J] v).inv ≫ ·)
          (TopCat.Presheaf.stalkFunctor_map_germ U x hxU (Φ.map f).hom)
      _ = _ := by erw [← Category.assoc, ← hn, Category.assoc]
  have hΦ := (extensionFullyFaithful k hp).map_bijective D[J] D[K]
  refine ⟨?_, ?_⟩
  · intro f g h
    obtain ⟨f, rfl⟩ := hΦ.2 f
    obtain ⟨g, rfl⟩ := hΦ.2 g
    have h' := (he f).symm.trans ((congrArg ((e J).homCongr (e K)) h).trans (he g))
    exact congrArg Φ.map (diagramEval_injective k hv hv' h')
  · intro g
    obtain ⟨f, hf⟩ := diagramEval_surjective k hv hv' harrow ((e J).homCongr (e K) g)
    exact ⟨Φ.map f, ((e J).homCongr (e K)).injective ((he f).trans hf)⟩

end TDA.Sheaf.RealConstructible
