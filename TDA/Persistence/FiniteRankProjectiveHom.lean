import TDA.Persistence.FiniteRankProjectiveResolutionKan

/-!
# Morphisms between rank-projective hooks

Morphisms between finite and infinite-death hooks are controlled by their
endpoint pairs. A nonzero map exists precisely when the target pair lies below
the source pair and the interval between them avoids the diagonal. The
normalized maps compose unless their composite interval meets the diagonal.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteRankProjectiveHom

open CategoryTheory

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]

private theorem smul_app_apply {M N : PModule.{u,0,u} k P}
    (f : M ⟶ N) (c : k) (p : P) (x : M.obj p) :
    (((c • f).app p).hom x) = c • ((f.app p).hom x) := by
  change ((c • (f.app p).hom) x) = c • ((f.app p).hom x)
  rfl

/-- The finite and infinite hook tags used by finite rank-projective covers. -/
abbrev HookTag (P : Type) [PartialOrder P] :=
  FiniteRankProjectiveClassification.RankProjectiveHookTag P

/-- The actual persistence module represented by a finite or infinite hook tag. -/
noncomputable abbrev hookModule (t : HookTag P) : PModule.{u,0,u} k P :=
  FiniteRankProjectiveClassification.rankProjectiveHookModule (k := k) t

/-- The birth endpoint of a hook tag. -/
def birth (t : HookTag P) : P :=
  match t with
  | .inl ab => ab.val.1
  | .inr a => a

/-- The death endpoint, with `⊤` denoting infinite death. -/
def death (t : HookTag P) : WithTop P :=
  match t with
  | .inl ab => ab.val.2
  | .inr _ => ⊤

/-- The endpoint pair of a tagged hook. -/
def endpoints (t : HookTag P) : P × WithTop P := (birth t, death t)

/-- Endpoint criterion for a morphism from `s` to `t`: the target interval is
below the source interval and contains no diagonal point between them. -/
def HomCondition (s t : HookTag P) : Prop :=
  (endpoints t).1 ≤ (endpoints s).1 ∧
    (endpoints t).2 ≤ (endpoints s).2 ∧
    ¬ (endpoints t).2 ≤ (endpoints s).1

@[simp] theorem homCondition_finite_finite (ab cd : FiniteHookDeflation.StrictPair P) :
    HomCondition (.inl ab) (.inl cd) ↔
      cd.val.1 ≤ ab.val.1 ∧ cd.val.2 ≤ ab.val.2 ∧ ¬ cd.val.2 ≤ ab.val.1 := by
  simp [HomCondition, endpoints, birth, death]

@[simp] theorem homCondition_finite_infinite (ab : FiniteHookDeflation.StrictPair P)
    (c : P) : ¬ HomCondition (.inl ab) (.inr c) := by
  simp [HomCondition, endpoints, birth, death]

@[simp] theorem homCondition_infinite_finite (a : P)
    (cd : FiniteHookDeflation.StrictPair P) :
    HomCondition (.inr a) (.inl cd) ↔
      cd.val.1 ≤ a ∧ ¬ cd.val.2 ≤ a := by
  simp [HomCondition, endpoints, birth, death]

@[simp] theorem homCondition_infinite_infinite (a b : P) :
    HomCondition (.inr a) (.inr b) ↔ b ≤ a := by
  simp [HomCondition, endpoints, birth, death]

/-- The unit at the birth endpoint of a finite hook or principal upset. -/
noncomputable def birthUnit (t : HookTag P) : (hookModule (k := k) t).obj (birth t) := by
  cases t with
  | inl ab =>
      exact SupportInterval.one (Hook.support ab.val.1 ab.val.2)
        (Hook.birth_mem ab.property)
  | inr a =>
      exact HookInfinity.birth a

/-- Transport the canonical birth unit of a hook to any point above its birth. -/
noncomputable def unitAt (t : HookTag P) (p : P) (hp : birth t ≤ p) :
    (hookModule (k := k) t).obj p :=
  structureMapLinear (hookModule (k := k) t) hp (birthUnit (k := k) t)

/-- The transported birth unit is nonzero exactly while the hook is supported. -/
theorem unitAt_ne_zero (t : HookTag P) (p : P) (hp : birth t ≤ p)
    (hdeath : ¬ death t ≤ p) : unitAt (k := k) t p hp ≠ 0 := by
  cases t with
  | inl ab =>
      have hmem : p ∈ Hook.support ab.val.1 ab.val.2 := by
        refine ⟨hp, ?_⟩
        intro h
        exact hdeath (by simpa [death] using h)
      intro hzero
      have hval := congrArg Subtype.val hzero
      change ((structureMapLinear (Hook.module (k := k) ab.val.1 ab.val.2)
        hp (SupportInterval.one (Hook.support ab.val.1 ab.val.2)
          (Hook.birth_mem ab.property))) : k) = 0 at hval
      rw [SupportInterval.structureMap_val] at hval
      simp [hmem, SupportInterval.one] at hval
  | inr a =>
      intro hzero
      have hpa : a ≤ p := by simpa [birth] using hp
      have hunit : HookInfinity.fiberEquivOfLe (R := k) hpa
          (unitAt (k := k) (.inr a) p hp) = 1 := by
        change HookInfinity.fiberEquivOfLe (R := k) hpa
          (structureMapLinear (HookInfinity.module (R := k) a) hpa
            (HookInfinity.birth (R := k) a)) = 1
        rw [HookInfinity.fiberEquivOfLe_structureMap
          (R := k) (le_refl a) hpa, HookInfinity.fiberEquiv_birth]
      have hzero' : unitAt (k := k) (.inr a) p hp = 0 := hzero
      have hval := congrArg (HookInfinity.fiberEquivOfLe (R := k) hpa) hzero'
      have hone : (1 : k) = 0 := by
        calc
          1 = HookInfinity.fiberEquivOfLe (R := k) hpa
              (unitAt (k := k) (.inr a) p hp) := hunit.symm
          _ = HookInfinity.fiberEquivOfLe (R := k) hpa 0 := hval
          _ = 0 := map_zero _
      exact one_ne_zero hone

private theorem finiteTargetMapZero
    (ab cd : FiniteHookDeflation.StrictPair P)
    (h : HomCondition (.inl ab) (.inl cd)) :
    structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2) ab.property.le
      (unitAt (k := k) (.inl cd) ab.val.1 h.1) = 0 := by
  have hc : cd.val.1 ≤ ab.val.1 ∧ cd.val.2 ≤ ab.val.2 ∧
      ¬ cd.val.2 ≤ ab.val.1 := by
    simpa [HomCondition, endpoints, birth, death] using h
  have htargetZero : structureMapLinear
      (Hook.module (k := k) cd.val.1 cd.val.2) (hc.1.trans ab.property.le) = 0 := by
    exact SupportInterval.structureMap_eq_zero_of_not_mem
      (Hook.support cd.val.1 cd.val.2)
      (Hook.support_ordConnected cd.val.1 cd.val.2)
      (hc.1.trans ab.property.le) (fun hx => hx.2.2 hc.2.1)
  change structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2)
      ab.property.le
      (structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2)
        hc.1 (SupportInterval.one (Hook.support cd.val.1 cd.val.2)
          (Hook.birth_mem cd.property))) = 0
  have hcv : structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2)
      ab.property.le
        (structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2)
          hc.1 (SupportInterval.one (Hook.support cd.val.1 cd.val.2)
            (Hook.birth_mem cd.property))) =
      structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2)
        (hc.1.trans ab.property.le)
        (SupportInterval.one (Hook.support cd.val.1 cd.val.2)
          (Hook.birth_mem cd.property)) := by
    simpa only [LinearMap.comp_apply] using
      (congrArg
        (fun f : (Hook.module (k := k) cd.val.1 cd.val.2).obj cd.val.1 →ₗ[k]
            (Hook.module (k := k) cd.val.1 cd.val.2).obj ab.val.2 =>
          f (SupportInterval.one (Hook.support cd.val.1 cd.val.2)
            (Hook.birth_mem cd.property)))
        (structureMapLinear_comp (Hook.module (k := k) cd.val.1 cd.val.2)
          hc.1 ab.property.le)).symm
  rw [hcv, htargetZero, LinearMap.zero_apply]

/-- The canonical nonzero map from a tagged hook when the target interval lies
below the source interval without crossing a diagonal pair. -/
noncomputable def normalizedHom (s t : HookTag P) (h : HomCondition s t) :
    hookModule (k := k) s ⟶ hookModule (k := k) t := by
  cases s with
  | inl ab =>
      cases t with
      | inl cd =>
          refine Hook.fromGenerator ab.property (hookModule (k := k) (.inl cd))
            (unitAt (k := k) (.inl cd) ab.val.1
              (by simpa [HomCondition, endpoints, birth, death] using h.1))
            (finiteTargetMapZero (k := k) ab cd h)
      | inr c =>
          simp [HomCondition, endpoints, birth, death] at h
  | inr a =>
      cases t with
      | inl cd =>
          have hc : cd.val.1 ≤ a ∧ ¬ cd.val.2 ≤ a := by
            simpa [HomCondition, endpoints, birth, death] using h
          exact HookInfinity.fromBirth a (hookModule (k := k) (.inl cd))
            (unitAt (k := k) (.inl cd) a (by simpa [birth] using hc.1))
      | inr b =>
          have hc : b ≤ a := by
            simpa [HomCondition, endpoints, birth, death] using h
          exact HookInfinity.fromBirth a (hookModule (k := k) (.inr b))
            (unitAt (k := k) (.inr b) a (by simpa [birth] using hc))

/-- The normalized morphism sends the source birth unit to the target's unit
at that grade. -/
@[simp] theorem normalizedHom_app_birth (s t : HookTag P) (h : HomCondition s t) :
    ((normalizedHom (k := k) s t h).app (birth s)).hom (birthUnit (k := k) s) =
      unitAt (k := k) t (birth s) h.1 := by
  cases s with
  | inl ab =>
      cases t with
      | inl cd =>
          have hp : cd.val.1 ≤ ab.val.1 := by
            simpa [HomCondition, endpoints, birth, death] using h.1
          change ((Hook.fromGenerator ab.property (hookModule (k := k) (.inl cd))
              (unitAt (k := k) (.inl cd) ab.val.1 hp)
              (finiteTargetMapZero (k := k) ab cd h)).app ab.val.1).hom
              (SupportInterval.one (Hook.support ab.val.1 ab.val.2)
                (Hook.birth_mem ab.property)) =
            unitAt (k := k) (.inl cd) ab.val.1 h.1
          exact Hook.fromGenerator_birth ab.property _ _ _
      | inr c => simp [HomCondition, endpoints, birth, death] at h
  | inr a =>
      cases t with
      | inl cd =>
          change ((HookInfinity.fromBirth a (hookModule (k := k) (.inl cd))
              (unitAt (k := k) (.inl cd) a
                (by simpa [HomCondition, endpoints, birth, death] using h.1))).app a).hom
              (HookInfinity.birth a) = unitAt (k := k) (.inl cd) a h.1
          exact HookInfinity.fromBirth_birth a _ _
      | inr b =>
          change ((HookInfinity.fromBirth a (hookModule (k := k) (.inr b))
              (unitAt (k := k) (.inr b) a
                (by simpa [HomCondition, endpoints, birth, death] using h.1))).app a).hom
              (HookInfinity.birth a) = unitAt (k := k) (.inr b) a h.1
          exact HookInfinity.fromBirth_birth a _ _

/-! The hook fibers are cyclic on their active support, with the birth unit as
the canonical generator. -/

/-- Read the coefficient of a vector in a hook fiber from its birth generator. -/
noncomputable def unitCoefficient (t : HookTag P) (p : P) (hp : birth t ≤ p)
    (x : (hookModule (k := k) t).obj p) : k := by
  cases t with
  | inl cd => exact x.val
  | inr a => exact HookInfinity.fiberEquivOfLe (R := k) (by simpa [birth] using hp) x

/-- Every vector in a hook fiber is its birth unit multiplied by its unique
coefficient. In an inactive finite-hook fiber both sides are zero. -/
theorem unitAt_span (t : HookTag P) (p : P) (hp : birth t ≤ p)
    (x : (hookModule (k := k) t).obj p) :
    x = unitCoefficient (k := k) t p hp x • unitAt (k := k) t p hp := by
  classical
  cases t with
  | inl cd =>
      let S := Hook.support cd.val.1 cd.val.2
      have hbirth : cd.val.1 ≤ p := by simpa [birth] using hp
      change SupportInterval.fiber (k := k) S p at x
      let u : SupportInterval.fiber (k := k) S p :=
        unitAt (k := k) (.inl cd) p hp
      have hunitval : u.val = if p ∈ S then 1 else 0 := by
        change (structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2)
          hbirth
          (SupportInterval.one S (Hook.birth_mem cd.property)) : k) = _
        rw [SupportInterval.structureMap_val S (Hook.support_ordConnected cd.val.1 cd.val.2)
          hbirth (SupportInterval.one S (Hook.birth_mem cd.property))]
        simp [S, SupportInterval.one]
      have hxval : x.val = if p ∈ S then x.val else 0 := by
        by_cases hmem : p ∈ S
        · simp [hmem]
        · simp [hmem, SupportInterval.val_eq_zero S hmem x]
      apply Subtype.ext
      change x.val = x.val * u.val
      rw [hxval, hunitval]
      by_cases hmem : p ∈ S <;> simp [hmem]
  | inr a =>
      have hpa : a ≤ p := by simpa [birth] using hp
      change (HookInfinity.module (R := k) a).obj p at x
      let u : (HookInfinity.module (R := k) a).obj p :=
        unitAt (k := k) (.inr a) p hp
      have hu : HookInfinity.fiberEquivOfLe (R := k) hpa u = 1 := by
        change HookInfinity.fiberEquivOfLe (R := k) hpa
          (structureMapLinear (HookInfinity.module (R := k) a) hpa
            (HookInfinity.birth (R := k) a)) = 1
        rw [HookInfinity.fiberEquivOfLe_structureMap (R := k) (le_rfl : a ≤ a) hpa,
          HookInfinity.fiberEquiv_birth]
      apply (HookInfinity.fiberEquivOfLe (R := k) hpa).injective
      change HookInfinity.fiberEquivOfLe (R := k) hpa x =
        HookInfinity.fiberEquivOfLe (R := k) hpa
          (unitCoefficient (k := k) (.inr a) p hp x • u)
      rw [map_smul, hu]
      simp only [unitCoefficient, smul_eq_mul, mul_one]

/-- Every morphism between two hooks satisfying the endpoint criterion is a
scalar multiple of the normalized generator. -/
theorem hom_eq_smul_normalized (s t : HookTag P) (h : HomCondition s t)
    (f : hookModule (k := k) s ⟶ hookModule (k := k) t) :
    ∃ c : k, f = c • normalizedHom (k := k) s t h := by
  let m := (f.app (birth s)).hom (birthUnit (k := k) s)
  let c := unitCoefficient (k := k) t (birth s) h.1 m
  have hspan := unitAt_span (k := k) t (birth s) h.1 m
  refine ⟨c, ?_⟩
  cases s with
  | inl ab =>
      cases t with
      | inl cd =>
          let f' : hookModule (k := k) (.inl ab) ⟶ hookModule (k := k) (.inl cd) := f
          let g : hookModule (k := k) (.inl ab) ⟶ hookModule (k := k) (.inl cd) :=
            normalizedHom (k := k) (.inl ab) (.inl cd) h
          apply Hook.hom_ext ab.property
          have hnorm : (g.app ab.val.1).hom
              (SupportInterval.one (Hook.support ab.val.1 ab.val.2)
                (Hook.birth_mem ab.property)) =
              unitAt (k := k) (.inl cd) ab.val.1 h.1 := by
            exact normalizedHom_app_birth (k := k) (.inl ab) (.inl cd) h
          have hfirst : (f'.app ab.val.1).hom
              (SupportInterval.one (Hook.support ab.val.1 ab.val.2)
                (Hook.birth_mem ab.property)) = m := rfl
          have hsecond : m = c • unitAt (k := k) (.inl cd) ab.val.1 h.1 := by
            change m = unitCoefficient (k := k) (.inl cd) ab.val.1 h.1 m •
              unitAt (k := k) (.inl cd) ab.val.1 h.1
            exact hspan
          have hthird : c • unitAt (k := k) (.inl cd) ab.val.1 h.1 =
              c • (g.app ab.val.1).hom
                (SupportInterval.one (Hook.support ab.val.1 ab.val.2)
                  (Hook.birth_mem ab.property)) := by rw [hnorm]
          exact hfirst.trans (hsecond.trans hthird)
      | inr b => exact (homCondition_finite_infinite ab b h).elim
  | inr a =>
      cases t with
      | inl cd =>
          let f' : hookModule (k := k) (.inr a) ⟶ hookModule (k := k) (.inl cd) := f
          let g : hookModule (k := k) (.inr a) ⟶ hookModule (k := k) (.inl cd) :=
            normalizedHom (k := k) (.inr a) (.inl cd) h
          apply HookInfinity.hom_ext
          have hnorm : (g.app a).hom (HookInfinity.birth a) =
              unitAt (k := k) (.inl cd) a h.1 := by
            exact normalizedHom_app_birth (k := k) (.inr a) (.inl cd) h
          have hfirst : (f'.app a).hom (HookInfinity.birth a) = m := rfl
          have hsecond : m = c • unitAt (k := k) (.inl cd) a h.1 := by
            change m = unitCoefficient (k := k) (.inl cd) a h.1 m •
              unitAt (k := k) (.inl cd) a h.1
            exact hspan
          have hthird : c • unitAt (k := k) (.inl cd) a h.1 =
              c • (g.app a).hom (HookInfinity.birth a) := by rw [hnorm]
          exact hfirst.trans (hsecond.trans hthird)
      | inr b =>
          let f' : hookModule (k := k) (.inr a) ⟶ hookModule (k := k) (.inr b) := f
          let g : hookModule (k := k) (.inr a) ⟶ hookModule (k := k) (.inr b) :=
            normalizedHom (k := k) (.inr a) (.inr b) h
          apply HookInfinity.hom_ext
          have hnorm : (g.app a).hom (HookInfinity.birth a) =
              unitAt (k := k) (.inr b) a h.1 := by
            exact normalizedHom_app_birth (k := k) (.inr a) (.inr b) h
          have hfirst : (f'.app a).hom (HookInfinity.birth a) = m := rfl
          have hsecond : m = c • unitAt (k := k) (.inr b) a h.1 := by
            change m = unitCoefficient (k := k) (.inr b) a h.1 m •
              unitAt (k := k) (.inr b) a h.1
            exact hspan
          have hthird : c • unitAt (k := k) (.inr b) a h.1 =
              c • (g.app a).hom (HookInfinity.birth a) := by rw [hnorm]
          exact hfirst.trans (hsecond.trans hthird)

/-- The scalar coefficient in the normalized-generator classification is
unique, so each nonzero hook Hom space is one-dimensional. -/
theorem hom_scalar_unique (s t : HookTag P) (h : HomCondition s t)
    (f : hookModule (k := k) s ⟶ hookModule (k := k) t) :
    ∃! c : k, f = c • normalizedHom (k := k) s t h := by
  obtain ⟨c, hc⟩ := hom_eq_smul_normalized (k := k) s t h f
  refine ⟨c, hc, ?_⟩
  intro d hd
  let n := normalizedHom (k := k) s t h
  have heq : c • n = d • n := hc.symm.trans hd
  have hca : ((c • n).app (birth s)).hom (birthUnit (k := k) s) =
      c • unitAt (k := k) t (birth s) h.1 := by
    calc
      _ = c • ((n.app (birth s)).hom (birthUnit (k := k) s)) :=
        smul_app_apply n c (birth s) (birthUnit (k := k) s)
      _ = c • unitAt (k := k) t (birth s) h.1 := by
        rw [normalizedHom_app_birth]
  have hda : ((d • n).app (birth s)).hom (birthUnit (k := k) s) =
      d • unitAt (k := k) t (birth s) h.1 := by
    calc
      _ = d • ((n.app (birth s)).hom (birthUnit (k := k) s)) :=
        smul_app_apply n d (birth s) (birthUnit (k := k) s)
      _ = d • unitAt (k := k) t (birth s) h.1 := by
        rw [normalizedHom_app_birth]
  have heval := congrArg
    (fun g : hookModule (k := k) s ⟶ hookModule (k := k) t =>
      (g.app (birth s)).hom (birthUnit (k := k) s)) heq
  have hscalar : c • unitAt (k := k) t (birth s) h.1 =
      d • unitAt (k := k) t (birth s) h.1 := hca.symm.trans (heval.trans hda)
  cases t with
  | inl cd =>
      let S := Hook.support cd.val.1 cd.val.2
      let u := unitAt (k := k) (.inl cd) (birth s) h.1
      have hbirth : cd.val.1 ≤ birth s := by
        simpa [endpoints, birth, death] using h.1
      have hdeath : ¬ cd.val.2 ≤ birth s := by
        simpa [endpoints, birth, death] using h.2.2
      have hmem : birth s ∈ S := ⟨hbirth, hdeath⟩
      have hunit : u.val = 1 := by
        change (structureMapLinear (Hook.module (k := k) cd.val.1 cd.val.2) hbirth
          (SupportInterval.one S (Hook.birth_mem cd.property)) : k) = 1
        rw [SupportInterval.structureMap_val]
        simp [S, hmem, SupportInterval.one]
      have hval := congrArg (fun x : SupportInterval.fiber (k := k) S (birth s) => x.val)
        hscalar
      change c * u.val = d * u.val at hval
      rw [hunit, mul_one, mul_one] at hval
      exact hval.symm
  | inr b =>
      let u := unitAt (k := k) (.inr b) (birth s) h.1
      change (HookInfinity.module (R := k) b).obj (birth s) at u
      have hba : b ≤ birth s := by simpa [endpoints, birth, death] using h.1
      have hunit : HookInfinity.fiberEquivOfLe (R := k) hba u = 1 := by
        change HookInfinity.fiberEquivOfLe (R := k) hba
          (structureMapLinear (HookInfinity.module (R := k) b) hba
            (HookInfinity.birth (R := k) b)) = 1
        rw [HookInfinity.fiberEquivOfLe_structureMap (R := k) (le_rfl : b ≤ b) hba,
          HookInfinity.fiberEquiv_birth]
      have hval := congrArg (HookInfinity.fiberEquivOfLe (R := k) hba) hscalar
      change HookInfinity.fiberEquivOfLe (R := k) hba (c • u) =
        HookInfinity.fiberEquivOfLe (R := k) hba (d • u) at hval
      simp only [LinearEquiv.map_smul, hunit, smul_eq_mul, mul_one] at hval
      simpa using hval.symm

/-! The Hom classification includes both existence and vanishing outside the
endpoint region. -/

/-- The normalized generator is nonzero exactly on its stated endpoint region. -/
theorem normalizedHom_ne_zero (s t : HookTag P) (h : HomCondition s t) :
    normalizedHom (k := k) s t h ≠ 0 := by
  intro hz
  have heval := congrArg
    (fun f : hookModule (k := k) s ⟶ hookModule (k := k) t =>
      (f.app (birth s)).hom (birthUnit (k := k) s)) hz
  rw [normalizedHom_app_birth] at heval
  exact unitAt_ne_zero (k := k) t (birth s) h.1 h.2.2 heval

/-- A nonzero map between finite rank-projective hooks can occur only when its
target endpoints lie below the source endpoints and the target has not died at
the source birth. -/
theorem hom_nonzero_implies_condition (s t : HookTag P)
    (f : hookModule (k := k) s ⟶ hookModule (k := k) t) (hf : f ≠ 0) :
    HomCondition s t := by
  have horder := FiniteRankProjectiveResolution.rankProjectiveHook_hom_nonzero_order
    s t f hf
  cases s with
  | inl ab =>
      cases t with
      | inl cd =>
          have ho : cd.val.1 ≤ ab.val.1 ∧ cd.val.2 ≤ ab.val.2 := by
            simpa [FiniteRankProjectiveResolution.rankProjectiveHookHomOrder] using horder
          have hdiagonal : ¬ cd.val.2 ≤ ab.val.1 := by
            intro hd
            have hnot : ab.val.1 ∉ Hook.support cd.val.1 cd.val.2 := by
              intro hx
              exact hx.2 hd
            have hzero : f = 0 := by
              apply Hook.hom_ext ab.property
              apply Subtype.ext
              exact SupportInterval.val_eq_zero (Hook.support cd.val.1 cd.val.2) hnot _
            exact hf hzero
          simpa [HomCondition, endpoints, birth, death] using
            ⟨ho.1, ho.2, hdiagonal⟩
      | inr b =>
          simp [FiniteRankProjectiveResolution.rankProjectiveHookHomOrder] at horder
  | inr a =>
      cases t with
      | inl cd =>
          have hbirth : cd.val.1 ≤ a := by
            simpa [FiniteRankProjectiveResolution.rankProjectiveHookHomOrder] using horder
          have hdiagonal : ¬ cd.val.2 ≤ a := by
            intro hd
            have hnot : a ∉ Hook.support cd.val.1 cd.val.2 := by
              intro hx
              exact hx.2 hd
            have hzero : f = 0 := by
              apply HookInfinity.hom_ext
              apply Subtype.ext
              exact SupportInterval.val_eq_zero (Hook.support cd.val.1 cd.val.2) hnot _
            exact hf hzero
          simpa [HomCondition, endpoints, birth, death] using And.intro hbirth hdiagonal
      | inr b =>
          simpa [HomCondition, endpoints, birth, death,
            FiniteRankProjectiveResolution.rankProjectiveHookHomOrder] using horder

/-- Existence of a nonzero map is equivalent to the endpoint criterion. -/
theorem exists_nonzero_hom_iff (s t : HookTag P) :
    (∃ f : hookModule (k := k) s ⟶ hookModule (k := k) t, f ≠ 0) ↔
      HomCondition s t := by
  constructor
  · rintro ⟨f, hf⟩
    exact hom_nonzero_implies_condition (k := k) s t f hf
  · intro h
    exact ⟨normalizedHom (k := k) s t h, normalizedHom_ne_zero (k := k) s t h⟩

/-- If the endpoint criterion fails, every map between the two hook modules is zero. -/
theorem hom_eq_zero_of_not_condition (s t : HookTag P) (h : ¬ HomCondition s t)
    (f : hookModule (k := k) s ⟶ hookModule (k := k) t) : f = 0 := by
  by_contra hf
  exact h (hom_nonzero_implies_condition (k := k) s t f hf)

/-! The normalization is preserved by structure maps on the source support. -/

/-- Naturality propagates the normalized coefficient from source birth along
every grade on which the source hook remains active. -/
theorem normalizedHom_app_unitAt (s t : HookTag P) (h : HomCondition s t)
    {p : P} (hp : birth s ≤ p) :
    ((normalizedHom (k := k) s t h).app p).hom
      (unitAt (k := k) s p hp) =
        unitAt (k := k) t p (h.1.trans hp) := by
  let f := normalizedHom (k := k) s t h
  have hnat : (f.app p).hom (unitAt (k := k) s p hp) =
      structureMapLinear (hookModule (k := k) t) hp
        ((f.app (birth s)).hom (birthUnit (k := k) s)) := by
    have hnatural := congrArg
      (fun g : (hookModule (k := k) s).obj (birth s) ⟶
          (hookModule (k := k) t).obj p => g.hom (birthUnit (k := k) s))
      (f.naturality (homOfLE hp))
    change (f.app p).hom
        (structureMapLinear (hookModule (k := k) s) hp (birthUnit (k := k) s)) =
      structureMapLinear (hookModule (k := k) t) hp
        ((f.app (birth s)).hom (birthUnit (k := k) s))
    exact hnatural
  have hcomp : structureMapLinear (hookModule (k := k) t) hp
      (unitAt (k := k) t (birth s) h.1) =
      unitAt (k := k) t p (h.1.trans hp) := by
    change structureMapLinear (hookModule (k := k) t) hp
        (structureMapLinear (hookModule (k := k) t) h.1 (birthUnit (k := k) t)) =
      structureMapLinear (hookModule (k := k) t) (h.1.trans hp)
        (birthUnit (k := k) t)
    exact (congrArg
      (fun g : (hookModule (k := k) t).obj (birth t) →ₗ[k]
          (hookModule (k := k) t).obj p => g (birthUnit (k := k) t))
      (structureMapLinear_comp (hookModule (k := k) t) h.1 hp)).symm
  rw [hnat, normalizedHom_app_birth]
  exact hcomp


/-- When the composite endpoints still avoid the diagonal, normalized maps
compose to the normalized map. -/
theorem normalizedHom_comp_of_condition (s t u : HookTag P)
    (hst : HomCondition s t) (htu : HomCondition t u) (hsu : HomCondition s u) :
    normalizedHom (k := k) s t hst ≫ normalizedHom (k := k) t u htu =
      normalizedHom (k := k) s u hsu := by
  let f := normalizedHom (k := k) s t hst
  let g := normalizedHom (k := k) t u htu
  have hbirth : ((f ≫ g).app (birth s)).hom (birthUnit (k := k) s) =
      ((normalizedHom (k := k) s u hsu).app (birth s)).hom
        (birthUnit (k := k) s) := by
    change (g.app (birth s)).hom
        ((f.app (birth s)).hom (birthUnit (k := k) s)) =
      ((normalizedHom (k := k) s u hsu).app (birth s)).hom
        (birthUnit (k := k) s)
    calc
      _ = (g.app (birth s)).hom
          (unitAt (k := k) t (birth s) hst.1) := by
        rw [normalizedHom_app_birth]
      _ = unitAt (k := k) u (birth s) (htu.1.trans hst.1) :=
        normalizedHom_app_unitAt (k := k) t u htu hst.1
      _ = ((normalizedHom (k := k) s u hsu).app (birth s)).hom
          (birthUnit (k := k) s) := by
        rw [normalizedHom_app_birth]
  cases s with
  | inl ab =>
      apply Hook.hom_ext ab.property
      change ((f ≫ g).app (birth (.inl ab))).hom (birthUnit (k := k) (.inl ab)) =
        ((normalizedHom (k := k) (.inl ab) u hsu).app (birth (.inl ab))).hom
          (birthUnit (k := k) (.inl ab))
      exact hbirth

  | inr a =>
      apply HookInfinity.hom_ext
      change ((f ≫ g).app (birth (.inr a))).hom (birthUnit (k := k) (.inr a)) =
        ((normalizedHom (k := k) (.inr a) u hsu).app (birth (.inr a))).hom
          (birthUnit (k := k) (.inr a))
      exact hbirth

/-- Endpoint order is transitive along a composable pair of admissible hook
maps. -/
theorem composite_endpoint_order (s t u : HookTag P)
    (hst : HomCondition s t) (htu : HomCondition t u) :
    birth u ≤ birth s ∧ death u ≤ death s :=
  ⟨htu.1.trans hst.1, htu.2.1.trans hst.2.1⟩

/-- If the composite endpoints cross the diagonal, the composite of the
normalized generators vanishes. -/
theorem normalizedHom_comp_of_not_condition (s t u : HookTag P)
    (hst : HomCondition s t) (htu : HomCondition t u)
    (hsu : ¬ HomCondition s u) :
    normalizedHom (k := k) s t hst ≫ normalizedHom (k := k) t u htu = 0 :=
  hom_eq_zero_of_not_condition (k := k) s u hsu _

/-- Under the endpoint order forced by the two input maps, the composite avoids
the diagonal exactly when the target has not died by the source birth. -/
theorem composite_condition_iff_no_diagonal (s t u : HookTag P)
    (hst : HomCondition s t) (htu : HomCondition t u) :
    HomCondition s u ↔ ¬ death u ≤ birth s := by
  obtain ⟨hbirth, hdeath⟩ := composite_endpoint_order s t u hst htu
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨hbirth, hdeath, h⟩

/-- Crossing the diagonal forces the normalized composite to vanish. -/
theorem normalizedHom_comp_of_diagonal (s t u : HookTag P)
    (hst : HomCondition s t) (htu : HomCondition t u)
    (hdiag : death u ≤ birth s) :
    normalizedHom (k := k) s t hst ≫ normalizedHom (k := k) t u htu = 0 :=
  normalizedHom_comp_of_not_condition (k := k) s t u hst htu
    (fun h => h.2.2 hdiag)

end TDA.Persistence.FiniteRankProjectiveHom
