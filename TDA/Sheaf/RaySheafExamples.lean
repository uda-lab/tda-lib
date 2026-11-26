import TDA.Sheaf.RaySheaf

/-!
# Ray sheaves: fixtures

These fixtures consume `TDA.Sheaf.RaySheaf` over a field `k`.

* The empty open: its ray cover is indexed by the empty type (`rayCover_bot_isEmpty`), and every
  sheaf `Q M` on the ray space is zero there (`rayQ_obj_bot_isZero`).
* The singleton module `pointModule`, `k` at `0` and zero elsewhere. All its strict maps vanish,
  so `Q (pointModule) = 0` (`isZero_rayQ_pointModule`) and `BQ(pointModule) = 0`, while the
  module itself is nonzero (`not_isZero_pointModule`). Hence it has distance zero to
  `BQ(pointModule)` (`pointModule_distance`), with an actual witness at every positive radius,
  but no witness at radius zero (`pointModule_isEmpty_zero`).
* The constant module `constModule` with identity maps: `Q (constModule)` is nonzero
  (`not_isZero_rayQ_constModule`) and the unit at `constModule` is an isomorphism
  (`isIso_rayUnit_constModule`), so here a radius-zero witness exists
  (`constModule_zeroInterleaving`).
-/

set_option autoImplicit false

namespace TDA.Sheaf.RaySheafExamples

open CategoryTheory Limits Opposite TopologicalSpace Topology TDA.Persistence TDA.Sheaf.RaySheaf
open scoped NNReal ZeroObject

/-! ## The empty open -/

/-- The ray cover of the empty open is indexed by the empty type. -/
theorem rayCover_bot_isEmpty :
    IsEmpty {p : ℝ // WithUpper.toUpper p ∈ (⊥ : Opens raySpace)} :=
  ⟨fun p => p.2⟩

/-- The empty open has the empty ray cover. -/
example : ⨆ i : {p : ℝ // WithUpper.toUpper p ∈ (⊥ : Opens raySpace)}, ray i.1 = ⊥ :=
  iSup_ray ⊥

variable {k : Type} [Field k]

/-- Every sheaf `Q M` of modules on the ray space is zero on the empty open. -/
theorem rayQ_obj_bot_isZero (M : PModule.{0,0,0} k ℝ) :
    IsZero (((rayQ (ModuleCat.{0} k)).obj M).presheaf.obj (op ⊥)) :=
  IsZero.of_iso (isZero_zero _)
    ((TopCat.Sheaf.isTerminalOfEmpty ((rayQ (ModuleCat.{0} k)).obj M)).uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

/-! ## The singleton module -/

/-- The fibre of the singleton module: `k` at `0` and zero elsewhere. -/
noncomputable def pointFiber (t : ℝ) : Submodule k k := by
  classical
  exact if t = 0 then ⊤ else ⊥

/-- The structure map of the singleton module: the identity at `0`, zero otherwise. -/
noncomputable def pointMap {s t : ℝ} (_h : s ≤ t) :
    pointFiber (k := k) s →ₗ[k] pointFiber (k := k) t := by
  classical
  exact if h : s = 0 ∧ t = 0 then Submodule.inclusion (by simp [pointFiber, h.1, h.2]) else 0

/-- The singleton module `k` supported at `0`. -/
noncomputable def pointModule : PModule.{0,0,0} k ℝ where
  obj t := ModuleCat.of k (pointFiber (k := k) t)
  map f := ModuleCat.ofHom (pointMap (leOfHom f))
  map_id t := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pointFiber (k := k) t at x
    change pointMap (k := k) (leOfHom (𝟙 t)) x = x
    apply Subtype.ext
    by_cases h : t = 0
    · simp [pointMap, h]
    · have hx : (x : k) = 0 := by
        simpa [pointFiber, h] using x.property
      simp [pointMap, h, hx]
  map_comp {s t r} f g := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    by_cases hs : s = 0
    · by_cases hr : r = 0
      · have ht : t = 0 := le_antisymm (hr ▸ leOfHom g) (hs ▸ leOfHom f)
        simp [pointMap, hs, ht, hr]
      · simp [pointMap, hr]
    · simp [pointMap, hs]

/-- Every strict map of the singleton module is zero. -/
theorem pointModule_map_lt {s t : ℝ} (h : s < t) :
    (pointModule (k := k)).map (homOfLE h.le) = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change pointMap (k := k) h.le x = 0
  have hst : ¬ (s = 0 ∧ t = 0) := fun h' => h.ne (h'.1.trans h'.2.symm)
  simp only [pointMap, hst, dite_false]
  rfl

/-- The singleton module is nonzero: its fibre at `0` is `k`. -/
theorem not_isZero_pointModule : ¬ IsZero (pointModule (k := k)) := by
  classical
  intro h
  have hz : Subsingleton (pointFiber (k := k) 0) :=
    ModuleCat.subsingleton_of_isZero (((Functor.isZero_iff _).1 h) 0)
  have h1 : (1 : k) ∈ pointFiber (k := k) 0 := by simp [pointFiber]
  have := congrArg Subtype.val (hz.elim ⟨1, h1⟩ 0)
  exact one_ne_zero this

/-- `Q` kills the singleton module. -/
theorem isZero_rayQ_pointModule : IsZero ((rayQ (ModuleCat.{0} k)).obj (pointModule (k := k))) :=
  (isZero_rayQ_iff _).2 fun _ _ h => pointModule_map_lt h

/-- `BQ` of the singleton module is zero. -/
theorem isZero_rayB_rayQ_pointModule :
    IsZero ((rayB _).obj ((rayQ (ModuleCat.{0} k)).obj (pointModule (k := k)))) :=
  (isZero_iff_isZero_rayB _).1 isZero_rayQ_pointModule

/-- At every positive radius, the singleton module is interleaved with `BQ` of it. -/
noncomputable example {ε : ℝ≥0} (hε : 0 < ε) :
    RealInterleaving ε (pointModule (k := k))
      ((rayB _).obj ((rayQ (ModuleCat.{0} k)).obj (pointModule (k := k)))) :=
  unitInterleaving _ hε

/-- The singleton module is at distance zero from `BQ` of it. -/
theorem pointModule_distance :
    realInterleavingDistance (pointModule (k := k))
      ((rayB _).obj ((rayQ (ModuleCat.{0} k)).obj (pointModule (k := k)))) = 0 :=
  realInterleavingDistance_rayB_rayQ _

/-- At radius zero there is no witness: it would be an isomorphism onto the zero module
`BQ(pointModule)`. -/
theorem pointModule_isEmpty_zero :
    IsEmpty (RealInterleaving 0 (pointModule (k := k))
      ((rayB _).obj ((rayQ (ModuleCat.{0} k)).obj (pointModule (k := k))))) :=
  ⟨fun i => not_isZero_pointModule (isZero_rayB_rayQ_pointModule.of_iso i.toIso)⟩

/-! ## The constant module -/

/-- The constant module `k` with identity maps. -/
noncomputable def constModule : PModule.{0,0,0} k ℝ :=
  (Functor.const ℝ).obj (ModuleCat.of k k)

/-- `Q` of the constant module is nonzero: its maps are identities. -/
theorem not_isZero_rayQ_constModule :
    ¬ IsZero ((rayQ (ModuleCat.{0} k)).obj (constModule (k := k))) := by
  intro h
  have h01 := (isZero_rayQ_iff _).1 h 0 1 one_pos
  have := congrArg (fun f : (constModule (k := k)).obj 0 ⟶ (constModule (k := k)).obj 1 =>
    (f.hom (1 : k) : k)) h01
  exact one_ne_zero (α := k) this

/-- For the constant module, all projections from `BQ(M)(t)` agree. -/
theorem rayProj_constModule {t a b : ℝ} (ha : t < a) (hb : t < b) :
    rayProj (constModule (k := k)) ha = rayProj (constModule (k := k)) hb :=
  ((Category.comp_id _).symm.trans
      (rayProj_comp_map (constModule (k := k)) ha (homOfLE (le_max_left a b)))).trans
    ((Category.comp_id _).symm.trans
      (rayProj_comp_map (constModule (k := k)) hb (homOfLE (le_max_right a b)))).symm

/-- The unit at the constant module is an isomorphism, with inverse a projection. -/
theorem isIso_rayUnit_constModule :
    IsIso ((rayUnit (ModuleCat.{0} k)).app (constModule (k := k))) := by
  have h : ∀ t : ℝ,
      IsIso (((rayUnit (ModuleCat.{0} k)).app (constModule (k := k))).app t) := fun t =>
    ⟨⟨rayProj (constModule (k := k)) (s := t + 1) (lt_add_one t), rayUnit_app_app_rayProj _ _,
      rayProj_ext _ fun _ hs => (Category.assoc _ _ _).trans
        ((congrArg (rayProj (constModule (k := k)) (lt_add_one t) ≫ ·)
          (rayUnit_app_app_rayProj _ hs)).trans
            (((Category.comp_id _).trans (rayProj_constModule (lt_add_one t) hs)).trans
              (Category.id_comp _).symm))⟩⟩
  exact NatIso.isIso_of_isIso_app _

/-- For the constant module, `M` and `BQ(M)` have a radius-zero witness. -/
noncomputable def constModule_zeroInterleaving :
    RealInterleaving 0 (constModule (k := k))
      ((rayB _).obj ((rayQ (ModuleCat.{0} k)).obj (constModule (k := k)))) :=
  haveI := isIso_rayUnit_constModule (k := k)
  RealInterleaving.ofIso (asIso ((rayUnit (ModuleCat.{0} k)).app (constModule (k := k))))

end TDA.Sheaf.RaySheafExamples
