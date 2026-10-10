import TDA.Reeb.CriticalValues
import TDA.Reeb.FiniteDiagram
import TDA.Reeb.IntervalCosheaf

/-!
# Constructible interval cosheaves are determined by finite data

For critical levels `S : CriticalValues n`, `S.IsConstructibleAt F` is the corrected form of
de Silva–Munch–Patel, Definition 3.9, for `F : OpenInterval ⥤ Type u`:

* every value `F I` is finite;
* for `I ≤ J` with `I` **nonempty** and `I`, `J` meeting the same levels, the actual inclusion
  map `F I → F J` is bijective;
* the values on the two exterior tails are empty (equivalently, on every interval inside them:
  `isEmpty_lowerTail_iff`, `isEmpty_upperTail_iff`).

The source omits the nonemptiness of `I`. Without it the rule would compare the empty value at
`⊥` with a nonempty value on a regular gap, since both meet no level; the strip fixture in
`ConstructibleCosheafExamples` refutes the uncorrected rule while satisfying the corrected one.
Arbitrary non-nested intervals with the same levels are never compared. The cosheaf condition
is a separate hypothesis. The predicate is invariant under refinement of the levels
(`IsConstructibleAt.of_refines`) and under natural isomorphism (`IsConstructibleAt.of_iso`).

`S.extract F` is the finite incidence data of Notation 3.11: vertex values `F (J i)` on stars,
edge values `F (K e)` on gaps, and the actual inclusion maps of `F` as endpoint functions.
`S.ShortMaps F G` collects functions on all stars and gaps commuting with both incidence maps;
these are exactly maps of the extracted data (`ShortMaps.equivHom`).

Main results, for interval cosheaves `F`, `G` (covers indexed in universe `0`, values in any
universe `u`) constructible at the same `S`:

* `natTransEquivShortMaps`: restriction `S.restrict` is an equivalence
  `(F ⟶ G) ≃ S.ShortMaps F G` (DMP Proposition 3.12). Its inverse `ShortMaps.extend` glues the
  short maps over the pieces of each envelope and transports along the envelope unit. Both
  inverse laws are proved (`ShortMaps.restrict_extend`, `ShortMaps.extend_restrict`), and a
  transformation is determined by its star and gap components (`natTrans_ext`).
* `natTransEquivDiagramHom`: the same equivalence with target the maps of extracted finite data.
* `isIso_iff_shortIntervals`: a transformation is an isomorphism exactly when all its star and
  gap components are bijective (DMP Corollary 3.14 and its converse); `ShortMaps.isIso_extend`
  is the form of Corollary 3.14 for extensions.
* `ShortMaps.extend_app_eq_starGlue`: on an interval that is its own envelope and meets a level,
  the extension is the map glued over the selected stars, whose compatibility comes from the
  incidence equations on adjacent stars and the empty value on `⊥` for nonadjacent ones.

Helper sections: gluing on the actual `IsIntervalCosheaf.existsUnique_glue`, local compatibility,
and transport of a transformation along a normalization `η : 𝟭 ⟶ N`. See
`docs/math/reeb-constructible-cosheaf.md`.
-/

open Set CategoryTheory TDA.Topology

universe u w

namespace TDA.Reeb

noncomputable section

open OpenInterval

/-! ### Gluing helpers on the actual `existsUnique_glue` -/

namespace IsIntervalCosheaf

section glue

variable {F : OpenInterval ⥤ Type u} (hF : IsIntervalCosheaf.{w} F)

/-- The glued map supplied by the cosheaf condition. -/
def glue {κ : Type w} (I : κ → OpenInterval) {J : OpenInterval}
    (hJ : ⋃ k, (I k : Set ℝ) = J) {A : Sort*} (a : ∀ k, F.obj (I k) → A)
    (ha : ∀ k l (c : F.obj (I k ⊓ I l)),
      a k (F.map (homOfLE inf_le_left) c) = a l (F.map (homOfLE inf_le_right) c)) :
    F.obj J → A :=
  (hF.existsUnique_glue I hJ a ha).exists.choose

variable {κ : Type w} {I : κ → OpenInterval} {J : OpenInterval} {hJ : ⋃ k, (I k : Set ℝ) = J}
  {A : Sort*} {a : ∀ k, F.obj (I k) → A}
  {ha : ∀ k l (c : F.obj (I k ⊓ I l)),
      a k (F.map (homOfLE inf_le_left) c) = a l (F.map (homOfLE inf_le_right) c)}

/-- Computation equation of the glued map, for any inclusion arrow. -/
theorem glue_map (k : κ) (h : I k ≤ J) (e : F.obj (I k)) :
    glue hF I hJ a ha (F.map (homOfLE h) e) = a k e := by
  rw [map_apply_eq_of_thin F (homOfLE h) (homOfLE (le_of_iUnion_eq hJ k))]
  exact (hF.existsUnique_glue I hJ a ha).exists.choose_spec k e

/-- Uniqueness of the glued map. -/
theorem eq_glue (g : F.obj J → A)
    (hg : ∀ k e, g (F.map (homOfLE (le_of_iUnion_eq hJ k)) e) = a k e) :
    g = glue hF I hJ a ha :=
  (hF.existsUnique_glue I hJ a ha).unique hg
    (hF.existsUnique_glue I hJ a ha).exists.choose_spec

/-- Cover refinement: if `I` covers `J`, `L` covers `H`, `J ≤ H`, each `I k` lies in `L (r k)`,
and `t ∘ a k = b (r k) ∘ F(I k ≤ L (r k))`, then `t ∘ glue a = glue b ∘ F(J ≤ H)`. -/
theorem glue_comp_map {μ : Type w} {L : μ → OpenInterval} {H : OpenInterval}
    {hH : ⋃ l, (L l : Set ℝ) = H} (hJH : J ≤ H) (r : κ → μ) (hr : ∀ k, I k ≤ L (r k))
    {B : Sort*} {b : ∀ l, F.obj (L l) → B}
    {hb : ∀ l l' (c : F.obj (L l ⊓ L l')),
      b l (F.map (homOfLE inf_le_left) c) = b l' (F.map (homOfLE inf_le_right) c)}
    (t : A → B) (ht : ∀ k e, t (a k e) = b (r k) (F.map (homOfLE (hr k)) e)) (x : F.obj J) :
    t (glue hF I hJ a ha x) = glue hF L hH b hb (F.map (homOfLE hJH) x) := by
  have hu := hF.existsUnique_glue I hJ (fun k e => t (a k e)) (fun k l c => congrArg t (ha k l c))
  have key : (fun x => t (glue hF I hJ a ha x)) =
      (fun x => glue hF L hH b hb (F.map (homOfLE hJH) x)) := by
    refine hu.unique (fun k e => ?_) (fun k e => ?_)
    · exact congrArg t (glue_map hF k _ e)
    · show glue hF L hH b hb (F.map (homOfLE hJH) (F.map (homOfLE (le_of_iUnion_eq hJ k)) e)) =
        t (a k e)
      have hkH : I k ≤ H := (hr k).trans (le_of_iUnion_eq hH (r k))
      rw [map_map_apply_of_thin F _ _ (homOfLE hkH),
        ← map_map_apply_of_thin F (homOfLE (hr k)) (homOfLE (le_of_iUnion_eq hH (r k))),
        glue_map hF (r k), ht]
  exact congrFun key x

include hF in
/-- Joint surjectivity: every element of `F J` comes from a member of a cover of `J`. -/
theorem exists_map_eq (I : κ → OpenInterval) (hJ : ⋃ k, (I k : Set ℝ) = J) (x : F.obj J) :
    ∃ k, ∃ e : F.obj (I k), F.map (homOfLE (le_of_iUnion_eq hJ k)) e = x := by
  have h := (hF.existsUnique_glue I hJ (A := Prop) (fun _ _ => True) (fun _ _ _ => rfl)).unique
    (y₁ := fun _ => True) (y₂ := fun x => ∃ k, ∃ e : F.obj (I k),
      F.map (homOfLE (le_of_iUnion_eq hJ k)) e = x)
    (fun _ _ => rfl) (fun k e => eq_true ⟨k, e, rfl⟩)
  exact (congrFun h x).mp trivial

end glue

end IsIntervalCosheaf

/-! ### Local compatibility -/

section compat

variable {F G : OpenInterval ⥤ Type u}

/-- An inclusion of an interval into itself acts as the identity. -/
theorem map_self_apply {I : OpenInterval} (h : I ≤ I) (x : F.obj I) : F.map (homOfLE h) x = x :=
  (map_apply_eq_of_thin F _ (𝟙 I) x).trans (F.map_id_apply I x)

/-- Two intervals meeting inside `K`: compatibility follows from the two incidence equations. -/
theorem compat_of_inf_le {T Jk Jl K : OpenInterval} (hk : Jk ≤ T) (hl : Jl ≤ T)
    (hKk : K ≤ Jk) (hKl : K ≤ Jl) (hinf : Jk ⊓ Jl ≤ K)
    (sk : F.obj Jk → G.obj Jk) (sl : F.obj Jl → G.obj Jl) (g : F.obj K → G.obj K)
    (hgk : ∀ y, G.map (homOfLE hKk) (g y) = sk (F.map (homOfLE hKk) y))
    (hgl : ∀ y, G.map (homOfLE hKl) (g y) = sl (F.map (homOfLE hKl) y))
    (c : F.obj (Jk ⊓ Jl)) :
    G.map (homOfLE hk) (sk (F.map (homOfLE inf_le_left) c)) =
      G.map (homOfLE hl) (sl (F.map (homOfLE inf_le_right) c)) := by
  rw [← map_map_apply_of_thin F (homOfLE hinf) (homOfLE hKk) (homOfLE inf_le_left) c,
    ← map_map_apply_of_thin F (homOfLE hinf) (homOfLE hKl) (homOfLE inf_le_right) c,
    ← hgk, ← hgl, map_map_apply_of_thin G _ _ (homOfLE (hKk.trans hk)),
    map_map_apply_of_thin G _ _ (homOfLE (hKl.trans hl))]

/-- An interval inside `⊥` has empty value once `F ⊥` is empty. -/
theorem isEmpty_of_le_bot {I : OpenInterval} (hbot : IsEmpty (F.obj ⊥)) (h : I ≤ ⊥) :
    IsEmpty (F.obj I) :=
  ⟨fun c => hbot.false (F.map (homOfLE h) c)⟩

/-- A compatible family on a cover `L` pulls back along a refinement `I k ≤ L (r k)` to a
compatible family on `I`. -/
theorem compat_comp {κ μ : Type*} {I : κ → OpenInterval} {L : μ → OpenInterval} (r : κ → μ)
    (hr : ∀ k, I k ≤ L (r k)) {A : Sort*} (b : ∀ l, F.obj (L l) → A)
    (hb : ∀ l l' (c : F.obj (L l ⊓ L l')),
      b l (F.map (homOfLE inf_le_left) c) = b l' (F.map (homOfLE inf_le_right) c))
    (k l : κ) (c : F.obj (I k ⊓ I l)) :
    b (r k) (F.map (homOfLE (hr k)) (F.map (homOfLE inf_le_left) c)) =
      b (r l) (F.map (homOfLE (hr l)) (F.map (homOfLE inf_le_right) c)) := by
  have h := hb (r k) (r l) (F.map (homOfLE (inf_le_inf (hr k) (hr l))) c)
  rw [map_map_apply_of_thin F _ _ (homOfLE (inf_le_left.trans (hr k))),
    map_map_apply_of_thin F _ _ (homOfLE (inf_le_right.trans (hr l)))] at h
  rw [map_map_apply_of_thin F _ _ (homOfLE (inf_le_left.trans (hr k))),
    map_map_apply_of_thin F _ _ (homOfLE (inf_le_right.trans (hr l)))]
  exact h

end compat

/-! ### Transport along a normalization `η : 𝟭 ⟶ N` -/

section transport

variable (N : OpenInterval ⥤ OpenInterval) (η : 𝟭 OpenInterval ⟶ N)

/-- `F ⟶ N ⋙ F`, built from `Functor.leftUnitor` and `Functor.whiskerRight`. -/
def unitTo (F : OpenInterval ⥤ Type u) : F ⟶ N ⋙ F :=
  (Functor.leftUnitor F).inv ≫ Functor.whiskerRight η F

theorem unitTo_app (F : OpenInterval ⥤ Type u) (I : OpenInterval) :
    (unitTo N η F).app I = F.map (η.app I) := by
  simp [unitTo]

variable {N η} {F G : OpenInterval ⥤ Type u}

theorem isIso_unitTo (hG : ∀ I, Function.Bijective (G.map (η.app I))) :
    IsIso (unitTo N η G) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro I
  rw [unitTo_app, isIso_iff_bijective]
  exact hG I

/-- The transported transformation `α = a_F ≫ β ≫ a_G⁻¹`. -/
def transport (hG : ∀ I, Function.Bijective (G.map (η.app I)))
    (β : N ⋙ F ⟶ N ⋙ G) : F ⟶ G :=
  haveI := isIso_unitTo hG
  unitTo N η F ≫ β ≫ inv (unitTo N η G)

variable (hG : ∀ I, Function.Bijective (G.map (η.app I))) (β : N ⋙ F ⟶ N ⋙ G)

/-- Defining square of the transported transformation. -/
theorem transport_comp_unitTo : transport hG β ≫ unitTo N η G = unitTo N η F ≫ β := by
  have := isIso_unitTo hG
  simp [transport]

theorem map_transport_app (I : OpenInterval) (x : F.obj I) :
    G.map (η.app I) ((transport hG β).app I x) = β.app I (F.map (η.app I) x) := by
  have h := congrArg (fun γ => γ.app I x) (transport_comp_unitTo hG β)
  simpa [unitTo_app] using h

/-- Pointwise formula `(G.map η_I)⁻¹ ∘ β_I ∘ F.map η_I`. -/
theorem transport_app (I : OpenInterval) (x : F.obj I) :
    (transport hG β).app I x = (Equiv.ofBijective _ (hG I)).symm (β.app I (F.map (η.app I) x)) :=
  (hG I).injective (by
    rw [Equiv.ofBijective_apply_symm_apply _ (hG I)]; exact map_transport_app hG β I x)

/-- Uniqueness of the transported transformation. -/
theorem eq_transport (α : F ⟶ G) (h : α ≫ unitTo N η G = unitTo N η F ≫ β) :
    α = transport hG β := by
  have := isIso_unitTo hG
  rw [← cancel_mono (unitTo N η G), h, transport_comp_unitTo]

/-- Pointwise uniqueness of the transported transformation. -/
theorem eq_transport_of_apply (α : F ⟶ G)
    (h : ∀ I x, G.map (η.app I) (α.app I x) = β.app I (F.map (η.app I) x)) :
    α = transport hG β := by
  refine eq_transport hG β α (NatTrans.ext (funext fun I => ?_))
  ext x
  simpa [unitTo_app] using h I x

end transport

namespace CriticalValues

variable {n : ℕ} (S : CriticalValues n)

/-! ### The corrected constructibility predicate -/

/-- Corrected constructibility (DMP Definition 3.9 with the nonempty-source correction): finite
values, bijective actual inclusion maps for nested `I ≤ J` with nonempty `I` and the same
levels, and empty values on the two exterior rays. The cosheaf condition is separate. -/
structure IsConstructibleAt (F : OpenInterval ⥤ Type u) : Prop where
  /-- Every value is finite. -/
  finite : ∀ I, Finite (F.obj I)
  /-- Inclusions of a nonempty interval into one meeting the same levels are bijective. -/
  bijective : ∀ ⦃I J : OpenInterval⦄ (h : I ≤ J), (I : Set ℝ).Nonempty →
    (∀ i, S.value i ∈ I ↔ S.value i ∈ J) → Function.Bijective (F.map (homOfLE h))
  /-- The value on the lower tail is empty. -/
  isEmpty_lowerTail : IsEmpty (F.obj S.lowerTail)
  /-- The value on the upper tail is empty. -/
  isEmpty_upperTail : IsEmpty (F.obj S.upperTail)

variable {S}

/-- The ray-only tail condition gives emptiness on every interval inside the lower tail. -/
theorem IsConstructibleAt.isEmpty_of_le_lowerTail {F : OpenInterval ⥤ Type u}
    (hF : S.IsConstructibleAt F) {I : OpenInterval} (h : I ≤ S.lowerTail) : IsEmpty (F.obj I) :=
  ⟨fun x => hF.isEmpty_lowerTail.false (F.map (homOfLE h) x)⟩

/-- The ray-only tail condition gives emptiness on every interval inside the upper tail. -/
theorem IsConstructibleAt.isEmpty_of_le_upperTail {F : OpenInterval ⥤ Type u}
    (hF : S.IsConstructibleAt F) {I : OpenInterval} (h : I ≤ S.upperTail) : IsEmpty (F.obj I) :=
  ⟨fun x => hF.isEmpty_upperTail.false (F.map (homOfLE h) x)⟩

/-- The ray-only lower tail condition is equivalent to emptiness on all intervals in the tail. -/
theorem isEmpty_lowerTail_iff (F : OpenInterval ⥤ Type u) :
    IsEmpty (F.obj S.lowerTail) ↔ ∀ I ≤ S.lowerTail, IsEmpty (F.obj I) :=
  ⟨fun h _ hI => ⟨fun x => h.false (F.map (homOfLE hI) x)⟩, fun h => h _ le_rfl⟩

/-- The ray-only upper tail condition is equivalent to emptiness on all intervals in the tail. -/
theorem isEmpty_upperTail_iff (F : OpenInterval ⥤ Type u) :
    IsEmpty (F.obj S.upperTail) ↔ ∀ I ≤ S.upperTail, IsEmpty (F.obj I) :=
  ⟨fun h _ hI => ⟨fun x => h.false (F.map (homOfLE hI) x)⟩, fun h => h _ le_rfl⟩

/-- Refinement invariance: constructibility at `S` gives constructibility at any `T` whose
levels include those of `S`. -/
theorem IsConstructibleAt.of_refines {m : ℕ} {T : CriticalValues m}
    (hST : Set.range S.value ⊆ Set.range T.value) {F : OpenInterval ⥤ Type u}
    (hF : S.IsConstructibleAt F) : T.IsConstructibleAt F where
  finite := hF.finite
  bijective _ _ h hI hhit := hF.bijective h hI fun i => by
    obtain ⟨j, hj⟩ := hST ⟨i, rfl⟩
    rw [← hj]
    exact hhit j
  isEmpty_lowerTail := hF.isEmpty_of_le_lowerTail (S.lowerTail_le_of_refines hST)
  isEmpty_upperTail := hF.isEmpty_of_le_upperTail (S.upperTail_le_of_refines hST)

/-- Invariance under natural isomorphism. -/
theorem IsConstructibleAt.of_iso {F G : OpenInterval ⥤ Type u} (e : F ≅ G)
    (hF : S.IsConstructibleAt F) : S.IsConstructibleAt G where
  finite I := by
    have := hF.finite I
    exact Finite.of_surjective _ ((isIso_iff_bijective (e.hom.app I)).1 inferInstance).2
  bijective I J h hI hhit := by
    have key : ⇑(G.map (homOfLE h)) = e.hom.app J ∘ F.map (homOfLE h) ∘ e.inv.app I := by
      funext y
      simp only [Function.comp_apply]
      rw [NatTrans.naturality_apply, Iso.inv_hom_id_app_apply]
    rw [key]
    exact ((isIso_iff_bijective (e.hom.app J)).1 inferInstance).comp
      ((hF.bijective h hI hhit).comp ((isIso_iff_bijective (e.inv.app I)).1 inferInstance))
  isEmpty_lowerTail := ⟨fun y => hF.isEmpty_lowerTail.false (e.inv.app _ y)⟩
  isEmpty_upperTail := ⟨fun y => hF.isEmpty_upperTail.false (e.inv.app _ y)⟩

variable (S)

/-! ### Extraction and short maps -/

/-- Extraction of finite data (DMP Notation 3.11): vertex values `F (J i)`, edge values
`F (K e)`, endpoint maps the actual inclusion maps of `F`. -/
def extract (F : OpenInterval ⥤ Type u) (hF : ∀ I, Finite (F.obj I)) : FiniteReebData.{u} n where
  V i := F.obj (S.J i)
  E e := F.obj (S.K e)
  finiteV _ := hF _
  finiteE _ := hF _
  left e x := F.map (homOfLE (S.K_le_J_castSucc e)) x
  right e x := F.map (homOfLE (S.K_le_J_succ e)) x

/-- The left endpoint function of the extracted data is the actual inclusion `K e ≤ J e`. -/
theorem extract_left (F : OpenInterval ⥤ Type u) (hF : ∀ I, Finite (F.obj I)) (e : Fin n)
    (x : F.obj (S.K e)) : (S.extract F hF).left e x = F.map (homOfLE (S.K_le_J_castSucc e)) x :=
  rfl

/-- The right endpoint function of the extracted data is the actual inclusion
`K e ≤ J (e + 1)`. -/
theorem extract_right (F : OpenInterval ⥤ Type u) (hF : ∀ I, Finite (F.obj I)) (e : Fin n)
    (x : F.obj (S.K e)) : (S.extract F hF).right e x = F.map (homOfLE (S.K_le_J_succ e)) x :=
  rfl

/-- Short-interval maps between precosheaves: functions on all stars and gaps commuting with
both actual incidence inclusions. -/
@[ext]
structure ShortMaps (F G : OpenInterval ⥤ Type u) where
  /-- Star components. -/
  star : ∀ i, F.obj (S.J i) → G.obj (S.J i)
  /-- Gap components. -/
  gap : ∀ e, F.obj (S.K e) → G.obj (S.K e)
  /-- Compatibility with the left incidence inclusions. -/
  left_comm : ∀ e x, G.map (homOfLE (S.K_le_J_castSucc e)) (gap e x) =
    star e.castSucc (F.map (homOfLE (S.K_le_J_castSucc e)) x)
  /-- Compatibility with the right incidence inclusions. -/
  right_comm : ∀ e x, G.map (homOfLE (S.K_le_J_succ e)) (gap e x) =
    star e.succ (F.map (homOfLE (S.K_le_J_succ e)) x)

variable {S}

namespace ShortMaps

variable {F G H : OpenInterval ⥤ Type u}

/-- Short maps are exactly maps of the extracted finite data. -/
def toHom (φ : S.ShortMaps F G) (hF : ∀ I, Finite (F.obj I)) (hG : ∀ I, Finite (G.obj I)) :
    (S.extract F hF).Hom (S.extract G hG) :=
  ⟨φ.star, φ.gap, φ.left_comm, φ.right_comm⟩

/-- Maps of the extracted finite data as short maps. -/
def ofHom {hF : ∀ I, Finite (F.obj I)} {hG : ∀ I, Finite (G.obj I)}
    (φ : (S.extract F hF).Hom (S.extract G hG)) : S.ShortMaps F G :=
  ⟨φ.v, φ.e, φ.left_comm, φ.right_comm⟩

/-- `toHom` and `ofHom` are inverse equivalences. -/
def equivHom (hF : ∀ I, Finite (F.obj I)) (hG : ∀ I, Finite (G.obj I)) :
    S.ShortMaps F G ≃ (S.extract F hF).Hom (S.extract G hG) where
  toFun φ := φ.toHom hF hG
  invFun φ := ofHom φ
  left_inv _ := rfl
  right_inv _ := rfl

/-- Identity short maps. -/
def id (F : OpenInterval ⥤ Type u) : S.ShortMaps F F :=
  ⟨fun _ => _root_.id, fun _ => _root_.id, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Composition of short maps, `φ` first. -/
def comp (φ : S.ShortMaps F G) (ψ : S.ShortMaps G H) : S.ShortMaps F H where
  star i := ψ.star i ∘ φ.star i
  gap e := ψ.gap e ∘ φ.gap e
  left_comm e x := (ψ.left_comm e _).trans (congrArg _ (φ.left_comm e x))
  right_comm e x := (ψ.right_comm e _).trans (congrArg _ (φ.right_comm e x))

/-- Inverse short maps from componentwise bijections; both incidence equations follow from
those of `φ`. -/
def inv (φ : S.ShortMaps F G) (hv : ∀ i, Function.Bijective (φ.star i))
    (he : ∀ e, Function.Bijective (φ.gap e)) : S.ShortMaps G F where
  star i := (Equiv.ofBijective _ (hv i)).symm
  gap e := (Equiv.ofBijective _ (he e)).symm
  left_comm e y := (hv e.castSucc).injective (by
    rw [← φ.left_comm, Equiv.ofBijective_apply_symm_apply _ (he e),
      Equiv.ofBijective_apply_symm_apply _ (hv e.castSucc)])
  right_comm e y := (hv e.succ).injective (by
    rw [← φ.right_comm, Equiv.ofBijective_apply_symm_apply _ (he e),
      Equiv.ofBijective_apply_symm_apply _ (hv e.succ)])

theorem comp_inv (φ : S.ShortMaps F G) (hv : ∀ i, Function.Bijective (φ.star i))
    (he : ∀ e, Function.Bijective (φ.gap e)) : φ.comp (φ.inv hv he) = ShortMaps.id F :=
  ShortMaps.ext (funext fun i => funext fun x => Equiv.ofBijective_symm_apply_apply _ (hv i) x)
    (funext fun e => funext fun x => Equiv.ofBijective_symm_apply_apply _ (he e) x)

theorem inv_comp (φ : S.ShortMaps F G) (hv : ∀ i, Function.Bijective (φ.star i))
    (he : ∀ e, Function.Bijective (φ.gap e)) : (φ.inv hv he).comp φ = ShortMaps.id G :=
  ShortMaps.ext (funext fun i => funext fun x => Equiv.ofBijective_apply_symm_apply _ (hv i) x)
    (funext fun e => funext fun x => Equiv.ofBijective_apply_symm_apply _ (he e) x)

end ShortMaps

variable (S)

/-- Restriction of a full natural transformation to star and gap data; both incidence squares
are naturality squares of `α`. -/
def restrict {F G : OpenInterval ⥤ Type u} (α : F ⟶ G) : S.ShortMaps F G where
  star i x := α.app (S.J i) x
  gap e x := α.app (S.K e) x
  left_comm _ x := (NatTrans.naturality_apply α _ x).symm
  right_comm _ x := (NatTrans.naturality_apply α _ x).symm

/-- Restriction as a map of extracted finite data, using the finiteness in the predicate. -/
def restrictHom {F G : OpenInterval ⥤ Type u} (hF : S.IsConstructibleAt F)
    (hG : S.IsConstructibleAt G) (α : F ⟶ G) :
    (S.extract F hF.finite).Hom (S.extract G hG.finite) :=
  (S.restrict α).toHom hF.finite hG.finite

theorem restrict_comp_star {F G H : OpenInterval ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H) (i)
    (x : F.obj (S.J i)) :
    (S.restrict (α ≫ β)).star i x = (S.restrict β).star i ((S.restrict α).star i x) := rfl

theorem restrict_comp_gap {F G H : OpenInterval ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H) (e)
    (x : F.obj (S.K e)) :
    (S.restrict (α ≫ β)).gap e x = (S.restrict β).gap e ((S.restrict α).gap e x) := rfl

theorem restrict_comp {F G H : OpenInterval ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H) :
    S.restrict (α ≫ β) = (S.restrict α).comp (S.restrict β) := rfl

theorem restrict_id (F : OpenInterval ⥤ Type u) : S.restrict (𝟙 F) = ShortMaps.id F := rfl

/-! ### Extension from short maps -/

variable {S} {F G : OpenInterval ⥤ Type u}

namespace ShortMaps

/-- Short maps on every piece; the tail values are empty for constructible `F`. -/
def onPiece (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F) :
    ∀ p : Piece n, F.obj (S.piece p) → G.obj (S.piece p)
  | .star i => φ.star i
  | .gap e => φ.gap e
  | .lowerTail => fun x => (hF.isEmpty_lowerTail.false x).elim
  | .upperTail => fun x => (hF.isEmpty_upperTail.false x).elim

/-- Naturality of the short maps for every inclusion of pieces: identities, the two incidence
inclusions of each gap, and inclusions out of the empty tails. -/
theorem onPiece_map (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F) {r p : Piece n}
    (h : S.piece r ≤ S.piece p) (x : F.obj (S.piece r)) :
    G.map (homOfLE h) (φ.onPiece hF r x) = φ.onPiece hF p (F.map (homOfLE h) x) := by
  cases r with
  | star i =>
    obtain rfl := S.value_mem_piece_iff.1 (h (S.value_mem_J i))
    rw [map_self_apply, map_self_apply]
  | gap e =>
    cases p with
    | star j =>
      rcases S.K_le_J_iff.1 h with rfl | rfl
      · exact φ.left_comm e x
      · exact φ.right_comm e x
    | gap e' =>
      obtain rfl := S.eq_of_K_le_K h
      rw [map_self_apply, map_self_apply]
    | lowerTail => exact absurd h (S.not_K_le_lowerTail e)
    | upperTail => exact absurd h (S.not_K_le_upperTail e)
  | lowerTail => exact (hF.isEmpty_lowerTail.false x).elim
  | upperTail => exact (hF.isEmpty_upperTail.false x).elim

/-- The family on the pieces below `U`: each piece map followed by the inclusion into `G U`. -/
def pieceFamily (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F) (U : OpenInterval)
    (p : {p : Piece n // S.piece p ≤ U}) : F.obj (S.piece p.1) → G.obj U :=
  fun x => G.map (homOfLE p.2) (φ.onPiece hF p.1 x)

/-- Compatibility of the piece family. An intersection of pieces is its own envelope, hence
covered by the pieces below it; on each such piece both sides are the piece map. -/
theorem pieceFamily_compat (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) (U : OpenInterval) (p q : {p : Piece n // S.piece p ≤ U})
    (c : F.obj (S.piece p.1 ⊓ S.piece q.1)) :
    φ.pieceFamily hF U p (F.map (homOfLE inf_le_left) c) =
      φ.pieceFamily hF U q (F.map (homOfLE inf_le_right) c) := by
  have hW := S.envelope_inf_of_eq (S.envelope_piece p.1) (S.envelope_piece q.1)
  obtain ⟨s, e, rfl⟩ := hFc.exists_map_eq
    (fun s : {s : Piece n // S.piece s ≤ S.piece p.1 ⊓ S.piece q.1} => S.piece s.1)
    (S.iUnion_piece_eq hW) c
  have hsp : S.piece s.1 ≤ S.piece p.1 := s.2.trans inf_le_left
  have hsq : S.piece s.1 ≤ S.piece q.1 := s.2.trans inf_le_right
  simp only [pieceFamily]
  rw [map_map_apply_of_thin F _ _ (homOfLE hsp), map_map_apply_of_thin F _ _ (homOfLE hsq),
    ← φ.onPiece_map hF hsp, ← φ.onPiece_map hF hsq,
    map_map_apply_of_thin G _ _ (homOfLE (hsp.trans p.2)),
    map_map_apply_of_thin G _ _ (homOfLE (hsq.trans q.2))]

/-- The extension on an interval that is its own envelope, glued over the pieces it contains. -/
def extendNormal (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) {U : OpenInterval} (hU : S.envelope U = U) :
    F.obj U → G.obj U :=
  hFc.glue (fun p : {p : Piece n // S.piece p ≤ U} => S.piece p.1) (S.iUnion_piece_eq hU)
    (φ.pieceFamily hF U) (φ.pieceFamily_compat hF hFc U)

variable (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)

/-- Computation of `extendNormal` on a piece. -/
theorem extendNormal_map {U : OpenInterval} (hU : S.envelope U = U) {p : Piece n}
    (h : S.piece p ≤ U) (x : F.obj (S.piece p)) :
    φ.extendNormal hF hFc hU (F.map (homOfLE h) x) = G.map (homOfLE h) (φ.onPiece hF p x) := by
  unfold extendNormal
  exact IsIntervalCosheaf.glue_map hFc
    (I := fun q : {q : Piece n // S.piece q ≤ U} => S.piece q.1) ⟨p, h⟩ h x

/-- Uniqueness of `extendNormal`. -/
theorem eq_extendNormal {U : OpenInterval} (hU : S.envelope U = U) (g : F.obj U → G.obj U)
    (hg : ∀ (p : Piece n) (h : S.piece p ≤ U) (x : F.obj (S.piece p)),
      g (F.map (homOfLE h) x) = G.map (homOfLE h) (φ.onPiece hF p x)) :
    g = φ.extendNormal hF hFc hU := by
  unfold extendNormal
  exact IsIntervalCosheaf.eq_glue hFc g fun p x => hg p.1 p.2 x

/-- Naturality of `extendNormal` for `U ≤ V`, by cover refinement: every piece below `U` is a
piece below `V`. This includes gaps at the fringe of `V`. -/
theorem extendNormal_comp_map {U V : OpenInterval} (hU : S.envelope U = U)
    (hV : S.envelope V = V) (hUV : U ≤ V) (x : F.obj U) :
    G.map (homOfLE hUV) (φ.extendNormal hF hFc hU x) =
      φ.extendNormal hF hFc hV (F.map (homOfLE hUV) x) := by
  unfold extendNormal
  exact IsIntervalCosheaf.glue_comp_map hFc
    (I := fun q : {q : Piece n // S.piece q ≤ U} => S.piece q.1)
    (L := fun q : {q : Piece n // S.piece q ≤ V} => S.piece q.1) hUV
    (fun p : {p : Piece n // S.piece p ≤ U} =>
      (⟨p.1, p.2.trans hUV⟩ : {p : Piece n // S.piece p ≤ V}))
    (fun _ => le_rfl) (G.map (homOfLE hUV)) (fun p e => by
      dsimp only [pieceFamily]
      rw [map_self_apply, map_map_apply_of_thin G _ _ (homOfLE (p.2.trans hUV))]) x

/-- The extension `β : N ⋙ F ⟶ N ⋙ G` over envelopes. -/
def envelopeExtension : S.envelopeFunctor ⋙ F ⟶ S.envelopeFunctor ⋙ G where
  app I := TypeCat.ofHom (φ.extendNormal hF hFc (S.envelope_envelope I))
  naturality I I' f := by
    ext x
    exact (φ.extendNormal_comp_map hF hFc (S.envelope_envelope I) (S.envelope_envelope I')
      (S.envelope_mono (leOfHom f)) x).symm

theorem envelopeExtension_app (I : OpenInterval) (x : F.obj (S.envelope I)) :
    (φ.envelopeExtension hF hFc).app I x = φ.extendNormal hF hFc (S.envelope_envelope I) x :=
  rfl

end ShortMaps

/-- Bridge for transport: if `N` preserves the levels met by nonempty intervals and sends empty
intervals to `⊥`, constructibility of `G` and the cosheaf condition (through `isEmpty_obj_bot`)
make every `G.map (η.app I)` bijective, including for empty `I`. -/
theorem _root_.TDA.Reeb.bijective_map_unit {N : OpenInterval ⥤ OpenInterval}
    {η : 𝟭 OpenInterval ⟶ N} (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{w} G)
    (hhit : ∀ I : OpenInterval, (I : Set ℝ).Nonempty → ∀ i, S.value i ∈ I ↔ S.value i ∈ N.obj I)
    (hbot : ∀ I : OpenInterval, ¬ (I : Set ℝ).Nonempty → N.obj I = ⊥) (I : OpenInterval) :
    Function.Bijective (G.map (η.app I)) := by
  by_cases hI : (I : Set ℝ).Nonempty
  · rw [← homOfLE_leOfHom (η.app I)]
    exact hG.bijective _ hI (hhit I hI)
  · have hle : I ≤ ⊥ := OpenInterval.le_iff_subset.2 fun x hx => (hI ⟨x, hx⟩).elim
    have h₁ := isEmpty_of_le_bot hGc.isEmpty_obj_bot hle
    have h₂ := isEmpty_of_le_bot hGc.isEmpty_obj_bot (hbot I hI).le
    exact ⟨fun a => (h₁.false a).elim, fun b => (h₂.false b).elim⟩

/-- For constructible `G` with empty value at `⊥`, every inclusion `G I → G (envelope I)` is
bijective, including for empty `I`. -/
theorem bijective_map_envelopeUnit (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{w} G)
    (I : OpenInterval) : Function.Bijective (G.map (S.envelopeUnit.app I)) :=
  bijective_map_unit hG hGc (fun _ hI i => (S.value_mem_envelope_iff hI i).symm)
    (fun _ hI => S.envelope_eq_bot hI) I

namespace ShortMaps

variable (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)
  (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G)

/-- The natural transformation extending short maps: `transport` of the envelope extension along
the envelope unit. -/
def extend : F ⟶ G :=
  transport (bijective_map_envelopeUnit hG hGc) (φ.envelopeExtension hF hFc)

/-- Defining property of the extension: after the inclusion into the envelope it is the glued
map on the envelope. -/
theorem map_extend_app (I : OpenInterval) (x : F.obj I) :
    G.map (homOfLE (S.le_envelope I)) ((φ.extend hF hFc hG hGc).app I x) =
      φ.extendNormal hF hFc (S.envelope_envelope I) (F.map (homOfLE (S.le_envelope I)) x) :=
  map_transport_app (bijective_map_envelopeUnit hG hGc) (φ.envelopeExtension hF hFc) I x

/-- The extension agrees with the short maps on every piece. -/
theorem extend_app_piece (p : Piece n) (x : F.obj (S.piece p)) :
    (φ.extend hF hFc hG hGc).app (S.piece p) x = φ.onPiece hF p x := by
  apply (bijective_map_envelopeUnit hG hGc (S.piece p)).injective
  refine (φ.map_extend_app hF hFc hG hGc _ x).trans ?_
  exact φ.extendNormal_map hF hFc (S.envelope_envelope _) (S.le_envelope _) x

/-- Restriction after extension is the identity. -/
theorem restrict_extend : S.restrict (φ.extend hF hFc hG hGc) = φ :=
  ShortMaps.ext (funext fun i => funext fun x => φ.extend_app_piece hF hFc hG hGc (.star i) x)
    (funext fun e => funext fun x => φ.extend_app_piece hF hFc hG hGc (.gap e) x)

theorem extend_app_J (i : Fin (n + 1)) (x : F.obj (S.J i)) :
    (φ.extend hF hFc hG hGc).app (S.J i) x = φ.star i x :=
  φ.extend_app_piece hF hFc hG hGc (.star i) x

theorem extend_app_K (e : Fin n) (x : F.obj (S.K e)) :
    (φ.extend hF hFc hG hGc).app (S.K e) x = φ.gap e x :=
  φ.extend_app_piece hF hFc hG hGc (.gap e) x

end ShortMaps

/-- On pieces, the short maps of a restriction are the components of the transformation. -/
theorem restrict_onPiece (α : F ⟶ G) (hF : S.IsConstructibleAt F) (p : Piece n)
    (x : F.obj (S.piece p)) : (S.restrict α).onPiece hF p x = α.app (S.piece p) x := by
  cases p with
  | star i => rfl
  | gap e => rfl
  | lowerTail => exact (hF.isEmpty_lowerTail.false x).elim
  | upperTail => exact (hF.isEmpty_upperTail.false x).elim

/-- Extension after restriction is the identity. -/
theorem ShortMaps.extend_restrict (α : F ⟶ G) (hF : S.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) (hG : S.IsConstructibleAt G)
    (hGc : IsIntervalCosheaf.{0} G) : (S.restrict α).extend hF hFc hG hGc = α := by
  refine (eq_transport_of_apply _ _ α fun I x => ?_).symm
  refine (NatTrans.naturality_apply α (S.envelopeUnit.app I) x).symm.trans ?_
  show α.app (S.envelope I) _ = (S.restrict α).extendNormal hF hFc (S.envelope_envelope I) _
  refine congrFun ((S.restrict α).eq_extendNormal hF hFc (S.envelope_envelope I)
    (fun y => α.app (S.envelope I) y) fun p h y => ?_) _
  dsimp only
  rw [NatTrans.naturality_apply, restrict_onPiece]

variable (S)

/-- **Finite determination of maps** (DMP Proposition 3.12). For interval cosheaves `F`, `G`
constructible at the same levels `S`, restriction to stars and gaps is an equivalence between
natural transformations `F ⟶ G` and short maps. -/
def natTransEquivShortMaps (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)
    (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G) :
    (F ⟶ G) ≃ S.ShortMaps F G where
  toFun := S.restrict
  invFun φ := φ.extend hF hFc hG hGc
  left_inv α := ShortMaps.extend_restrict α hF hFc hG hGc
  right_inv φ := φ.restrict_extend hF hFc hG hGc

/-- The same equivalence with target the maps of the extracted finite data. -/
def natTransEquivDiagramHom (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)
    (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G) :
    (F ⟶ G) ≃ (S.extract F hF.finite).Hom (S.extract G hG.finite) :=
  (S.natTransEquivShortMaps hF hFc hG hGc).trans (ShortMaps.equivHom hF.finite hG.finite)

theorem natTransEquivDiagramHom_apply (hF : S.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G)
    (α : F ⟶ G) : S.natTransEquivDiagramHom hF hFc hG hGc α = S.restrictHom hF hG α :=
  rfl

/-- Restriction to stars and gaps is injective. -/
theorem restrict_injective (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)
    (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G) :
    Function.Injective (S.restrict : (F ⟶ G) → S.ShortMaps F G) :=
  (S.natTransEquivShortMaps hF hFc hG hGc).injective

/-- Short-component extensionality: transformations agreeing on all stars and gaps are equal. -/
theorem natTrans_ext (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)
    (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G) {α β : F ⟶ G}
    (hJ : ∀ i x, α.app (S.J i) x = β.app (S.J i) x)
    (hK : ∀ e x, α.app (S.K e) x = β.app (S.K e) x) : α = β :=
  S.restrict_injective hF hFc hG hGc (ShortMaps.ext (funext fun i => funext fun x => hJ i x)
    (funext fun e => funext fun x => hK e x))

/-- **Isomorphism criterion** (DMP Corollary 3.14 and its converse). A transformation between
interval cosheaves constructible at `S` is an isomorphism exactly when all its star and gap
components are bijective. -/
theorem isIso_iff_shortIntervals (hF : S.IsConstructibleAt F) (hFc : IsIntervalCosheaf.{0} F)
    (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G) (α : F ⟶ G) :
    IsIso α ↔ (∀ i, Function.Bijective (α.app (S.J i))) ∧
      ∀ e, Function.Bijective (α.app (S.K e)) := by
  constructor
  · intro _
    exact ⟨fun i => (isIso_iff_bijective _).1 inferInstance,
      fun e => (isIso_iff_bijective _).1 inferInstance⟩
  · rintro ⟨hv, he⟩
    let ψ : S.ShortMaps G F := (S.restrict α).inv hv he
    refine ⟨⟨ψ.extend hG hGc hF hFc, ?_, ?_⟩⟩
    · apply S.restrict_injective hF hFc hF hFc
      rw [restrict_comp, restrict_id, ψ.restrict_extend]
      exact ShortMaps.comp_inv _ hv he
    · apply S.restrict_injective hG hGc hG hGc
      rw [restrict_comp, restrict_id, ψ.restrict_extend]
      exact ShortMaps.inv_comp _ hv he

/-- DMP Corollary 3.14 for extensions: short maps with bijective components extend to an
isomorphism. -/
theorem ShortMaps.isIso_extend (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G)
    (hv : ∀ i, Function.Bijective (φ.star i)) (he : ∀ e, Function.Bijective (φ.gap e)) :
    IsIso (φ.extend hF hFc hG hGc) := by
  refine (S.isIso_iff_shortIntervals hF hFc hG hGc _).2 ⟨fun i => ?_, fun e => ?_⟩
  · convert hv i using 1
    exact funext fun x => φ.extend_app_J hF hFc hG hGc i x
  · convert he e using 1
    exact funext fun x => φ.extend_app_K hF hFc hG hGc e x

/-! ### The selected-star gluing -/

variable {S}

namespace ShortMaps

/-- The selected-star family on `U`: each star map followed by the inclusion into `G U`. -/
def starFamily (φ : S.ShortMaps F G) {U : OpenInterval} (hU : S.envelope U = U)
    (i : {i : Fin (n + 1) // S.value i ∈ U}) : F.obj (S.J i.1) → G.obj U :=
  fun x => G.map (homOfLE ((S.J_le_envelope i.2).trans hU.le)) (φ.star i.1 x)

/-- Compatibility of the selected-star family: equal stars by thinness, adjacent stars through
their common gap and both incidence equations, nonadjacent stars through the empty value
at `⊥`. -/
theorem starFamily_compat (φ : S.ShortMaps F G) (hFc : IsIntervalCosheaf.{w} F)
    {U : OpenInterval} (hU : S.envelope U = U) (i j : {i : Fin (n + 1) // S.value i ∈ U})
    (c : F.obj (S.J i.1 ⊓ S.J j.1)) :
    φ.starFamily hU i (F.map (homOfLE inf_le_left) c) =
      φ.starFamily hU j (F.map (homOfLE inf_le_right) c) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [starFamily]
  rcases lt_trichotomy (i.val + 1) j.val with hlt | heq | hgt
  · exact ((isEmpty_of_le_bot hFc.isEmpty_obj_bot (S.J_inf_J_eq_bot hlt).le).false c).elim
  · have he : ∃ e : Fin n, i = e.castSucc ∧ j = e.succ :=
      ⟨⟨i.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩
    obtain ⟨e, rfl, rfl⟩ := he
    exact compat_of_inf_le _ _ (S.K_le_J_castSucc e) (S.K_le_J_succ e)
      (S.J_castSucc_inf_J_succ e).le _ _ (φ.gap e) (φ.left_comm e) (φ.right_comm e) c
  · rcases lt_trichotomy (j.val + 1) i.val with hlt' | heq' | hgt'
    · exact ((isEmpty_of_le_bot hFc.isEmpty_obj_bot
        (by rw [inf_comm]; exact (S.J_inf_J_eq_bot hlt').le)).false c).elim
    · have he : ∃ e : Fin n, j = e.castSucc ∧ i = e.succ :=
        ⟨⟨j.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩
      obtain ⟨e, rfl, rfl⟩ := he
      exact compat_of_inf_le _ _ (S.K_le_J_succ e) (S.K_le_J_castSucc e)
        (by rw [inf_comm]; exact (S.J_castSucc_inf_J_succ e).le) _ _ (φ.gap e)
        (φ.right_comm e) (φ.left_comm e) c
    · obtain rfl : i = j := Fin.ext (by omega)
      rw [map_apply_eq_of_thin F (homOfLE inf_le_left) (homOfLE inf_le_right) c]

/-- The map glued over the selected stars of an interval that is its own envelope and meets a
level. -/
def starGlue (φ : S.ShortMaps F G) (hFc : IsIntervalCosheaf.{0} F) {U : OpenInterval}
    (hU : S.envelope U = U) (hhit : ∃ i, S.value i ∈ U) : F.obj U → G.obj U :=
  hFc.glue (fun i : {i : Fin (n + 1) // S.value i ∈ U} => S.J i.1)
    ((S.iUnion_J_eq_envelope hhit).trans (congrArg _ hU)) (φ.starFamily hU) (φ.starFamily_compat hFc hU)

/-- On an interval that is its own envelope and meets a level, the extension is the map glued
over the selected stars. -/
theorem extend_app_eq_starGlue (φ : S.ShortMaps F G) (hF : S.IsConstructibleAt F)
    (hFc : IsIntervalCosheaf.{0} F) (hG : S.IsConstructibleAt G) (hGc : IsIntervalCosheaf.{0} G)
    {U : OpenInterval} (hU : S.envelope U = U) (hhit : ∃ i, S.value i ∈ U) :
    ⇑((φ.extend hF hFc hG hGc).app U) = φ.starGlue hFc hU hhit :=
  IsIntervalCosheaf.eq_glue hFc _ fun i x => by
    rw [NatTrans.naturality_apply, φ.extend_app_J hF hFc hG hGc]
    rfl

end ShortMaps

end CriticalValues

end

end TDA.Reeb
