import TDA.Sheaf.AlternatingDiagram

/-!
# Reflection at a sink of an alternating diagram

Let `p` be a sink of the orientation `o` and let `o'` reverse exactly the arrows at `p`. The
sink reflection replaces the space at `p` by the kernel of the signed sum of the incoming maps
(the fibre product of the two incoming maps at an interior vertex) and makes `p` a source whose
arrows are the coordinate projections. All other spaces and arrows are kept.

To avoid transporting spaces between vertices, every reflected space is a subspace of the
product `∀ l, M l` of all vertex spaces: at `j ≠ p` it is the copy of `M j`, at `p` it is the
kernel above. The reflection is an additive functor. It sends an interval diagram to the
interval diagram of `reflectInterval p J`, and it kills the singleton `{p}`.
-/

universe u

namespace TDA.Sheaf.AlternatingDiagram

open CategoryTheory Limits TDA.Persistence
open ZeroObject

variable {n : ℕ} {k : Type u} [Field k]

/-! ### Sinks, sources and reversed orientations -/

/-- No arrow leaves `p`. -/
def IsSink (o : Fin n → Bool) (p : Fin (n + 1)) : Prop := ∀ j, ¬ Arrow o p j

/-- No arrow enters `p`. -/
def IsSource (o : Fin n → Bool) (p : Fin (n + 1)) : Prop := ∀ i, ¬ Arrow o i p

/-- `o'` reverses exactly the arrows at `p`. -/
def IsFlipAt (o o' : Fin n → Bool) (p : Fin (n + 1)) : Prop :=
  ∀ i j, Arrow o' i j ↔ if i = p ∨ j = p then Arrow o j i else Arrow o i j

theorem IsFlipAt.symm {o o' : Fin n → Bool} {p : Fin (n + 1)} (h : IsFlipAt o o' p) :
    IsFlipAt o' o p := by
  intro i j
  by_cases hij : i = p ∨ j = p
  · have hji : j = p ∨ i = p := hij.symm
    simp only [hij, ite_true]
    rw [h j i]
    simp [hji]
  · simp only [hij, ite_false]
    rw [h i j]
    simp [hij]

/-- After reversing the arrows at a sink, it is a source. -/
theorem IsFlipAt.isSource {o o' : Fin n → Bool} {p : Fin (n + 1)} (h : IsFlipAt o o' p)
    (hs : IsSink o p) : IsSource o' p := by
  intro i hi
  rw [h i p] at hi
  simp only [or_true, ite_true] at hi
  exact hs i hi

/-- After reversing the arrows at a source, it is a sink. -/
theorem IsFlipAt.isSink {o o' : Fin n → Bool} {p : Fin (n + 1)} (h : IsFlipAt o o' p)
    (hs : IsSource o p) : IsSink o' p := by
  intro j hj
  rw [h p j] at hj
  simp only [true_or, ite_true] at hj
  exact hs j hj

/-- The sign attached to a neighbour of `p`: `1` on the left and `-1` on the right. -/
def sgn (p l : Fin (n + 1)) : k := if l < p then 1 else -1

theorem sgn_ne_zero (p l : Fin (n + 1)) : sgn (k := k) p l ≠ 0 := by
  unfold sgn; split_ifs <;> simp

/-! ### The sink reflection -/

variable {o o' : Fin n → Bool} {p : Fin (n + 1)}

/-- The product of all vertex spaces of a diagram. -/
abbrev Tot (M : Diagram k o) := ∀ l : Fin (n + 1), M.obj (vtx o l)

/-- The coordinate projection of the product of all vertex spaces. -/
abbrev pr (M : Diagram k o) (l : Fin (n + 1)) : Tot M →ₗ[k] M.obj (vtx o l) :=
  LinearMap.proj (R := k) (φ := fun l => M.obj (vtx o l)) l

/-- The coordinate inclusion into the product of all vertex spaces. -/
abbrev ins (M : Diagram k o) (l : Fin (n + 1)) : M.obj (vtx o l) →ₗ[k] Tot M :=
  LinearMap.single k (fun l => M.obj (vtx o l)) l

/-- The signed sum of the maps into `p`, on the product of all vertex spaces. -/
noncomputable def sinkSum (M : Diagram k o) (p : Fin (n + 1)) : Tot M →ₗ[k] M.obj (vtx o p) :=
  ∑ l, sgn (k := k) p l • (arr M l p ∘ₗ pr M l)

theorem sinkSum_apply (M : Diagram k o) (p : Fin (n + 1)) (x : Tot M) :
    sinkSum M p x = ∑ l, sgn (k := k) p l • arr M l p (x l) := by
  simp [sinkSum]

/-- The coordinates allowed in the reflected space at `j`: the in-neighbours of `p` at `p`,
and `j` itself elsewhere. -/
def sinkSupp (o : Fin n → Bool) (p j l : Fin (n + 1)) : Prop :=
  if j = p then Arrow o l p else l = j

instance sinkSuppDecidable (o : Fin n → Bool) (p j l : Fin (n + 1)) :
    Decidable (sinkSupp o p j l) := by
  unfold sinkSupp; infer_instance

/-- The reflected space at `j`, as a subspace of the product of all vertex spaces. -/
noncomputable def sinkSpace (M : Diagram k o) (p j : Fin (n + 1)) : Submodule k (Tot M) :=
  (⨅ l, ⨅ (_ : ¬ sinkSupp o p j l), LinearMap.ker (pr M l)) ⊓
    (if j = p then LinearMap.ker (sinkSum M p) else ⊤)

theorem mem_sinkSpace (M : Diagram k o) (p j : Fin (n + 1)) (x : Tot M) :
    x ∈ sinkSpace M p j ↔
      (∀ l, ¬ sinkSupp o p j l → x l = 0) ∧ (j = p → sinkSum M p x = 0) := by
  unfold sinkSpace
  by_cases hj : j = p
  · simp [hj, Submodule.mem_iInf]
  · simp [hj, Submodule.mem_iInf]

/-- The map of the reflected diagram along an arrow from `i` to `j`. -/
noncomputable def sinkLift (M : Diagram k o) (p i j : Fin (n + 1)) : Tot M →ₗ[k] Tot M := by
  classical
  exact if i = p then ins M j ∘ₗ pr M j else ins M j ∘ₗ arr M i j ∘ₗ pr M i

theorem sinkLift_apply_self (M : Diagram k o) {p i : Fin (n + 1)} (hi : i = p) (j : Fin (n + 1))
    (x : Tot M) : sinkLift M p i j x = Pi.single j (x j) := by
  simp [sinkLift, hi]

theorem sinkLift_apply_of_ne (M : Diagram k o) {p i : Fin (n + 1)} (hi : i ≠ p)
    (j : Fin (n + 1)) (x : Tot M) : sinkLift M p i j x = Pi.single j (arr M i j (x i)) := by
  simp [sinkLift, hi]

/-- The arrow maps of the reflection land in the reflected spaces. -/
theorem sinkLift_mem (M : Diagram k o) (hs : IsSink o p) (hf : IsFlipAt o o' p)
    {i j : Fin (n + 1)} (h : Arrow o' i j) (x : Tot M) :
    sinkLift M p i j x ∈ sinkSpace M p j := by
  have hj : j ≠ p := by
    rintro rfl
    rw [hf i j] at h
    simp only [or_true, ite_true] at h
    exact hs i h
  rw [mem_sinkSpace]
  refine ⟨fun l hl => ?_, fun h' => absurd h' hj⟩
  have hl' : l ≠ j := by simpa [sinkSupp, hj] using hl
  by_cases hi : i = p
  · rw [sinkLift_apply_self M hi]; simp [hl']
  · rw [sinkLift_apply_of_ne M hi]; simp [hl']

/-- A morphism of diagrams acting on the product of all vertex spaces. -/
noncomputable def totMap {M N : Diagram k o} (φ : M ⟶ N) : Tot M →ₗ[k] Tot N :=
  LinearMap.pi (fun l => (φ.app (vtx o l)).hom ∘ₗ pr M l)

@[simp]
theorem totMap_apply {M N : Diagram k o} (φ : M ⟶ N) (x : Tot M) (l : Fin (n + 1)) :
    totMap φ x l = (φ.app (vtx o l)).hom (x l) := rfl

theorem totMap_single {M N : Diagram k o} (φ : M ⟶ N) (j : Fin (n + 1))
    (v : M.obj (vtx o j)) :
    totMap φ (Pi.single j v) = Pi.single j ((φ.app (vtx o j)).hom v) := by
  funext l
  by_cases hl : l = j
  · subst hl; simp
  · simp [hl]

theorem sinkSum_totMap {M N : Diagram k o} (φ : M ⟶ N) (p : Fin (n + 1)) (x : Tot M) :
    sinkSum N p (totMap φ x) = (φ.app (vtx o p)).hom (sinkSum M p x) := by
  simp only [sinkSum_apply, totMap_apply, map_sum, map_smul, arr_naturality]

theorem totMap_mem {M N : Diagram k o} (φ : M ⟶ N) {p j : Fin (n + 1)} {x : Tot M}
    (hx : x ∈ sinkSpace M p j) : totMap φ x ∈ sinkSpace N p j := by
  rw [mem_sinkSpace] at hx ⊢
  refine ⟨fun l hl => ?_, fun hj => ?_⟩
  · simp [hx.1 l hl]
  · rw [sinkSum_totMap, hx.2 hj, map_zero]

theorem sinkLift_totMap {M N : Diagram k o} (φ : M ⟶ N) (p i j : Fin (n + 1)) (x : Tot M) :
    sinkLift N p i j (totMap φ x) = totMap φ (sinkLift M p i j x) := by
  by_cases hi : i = p
  · rw [sinkLift_apply_self _ hi, sinkLift_apply_self _ hi, totMap_single, totMap_apply]
  · rw [sinkLift_apply_of_ne _ hi, sinkLift_apply_of_ne _ hi, totMap_single, totMap_apply,
      arr_naturality]

variable (o')

/-- The reflection at a sink `p`, landing in diagrams on the orientation `o'` that reverses the
arrows at `p`. -/
noncomputable def reflectSink (hs : IsSink o p) (hf : IsFlipAt o o' p) :
    Diagram k o ⥤ Diagram k o' where
  obj M := ofArrows (fun j => ModuleCat.of k (sinkSpace M p j))
    (fun {i j} h => ModuleCat.ofHom ((sinkLift M p i j).restrict
      (fun x _ => sinkLift_mem M hs hf h x)))
  map φ := homMk (fun X => ModuleCat.ofHom ((totMap φ).restrict (fun _ hx => totMap_mem φ hx)))
    (fun {i j} h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      simp only [ofArrows_map_gen]
      exact (sinkLift_totMap φ p i j x.1).symm)
  map_id M := by
    ext X x
    rfl
  map_comp φ ψ := by
    ext X x
    rfl

variable {o'}

instance reflectSink_additive (hs : IsSink o p) (hf : IsFlipAt o o' p) :
    (reflectSink (k := k) o' hs hf).Additive where
  map_add := by
    intro M N φ ψ
    ext X x
    rfl

instance reflectSink_finiteDimensional (hs : IsSink o p) (hf : IsFlipAt o o' p)
    (M : Diagram k o) [∀ X, FiniteDimensional k (M.obj X)] (X : Paths (Vertex o')) :
    FiniteDimensional k (((reflectSink o' hs hf).obj M).obj X) := by
  change FiniteDimensional k (sinkSpace M p X)
  infer_instance

theorem reflectSink_obj_obj (hs : IsSink o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    (j : Fin (n + 1)) :
    ((reflectSink o' hs hf).obj M).obj (vtx o' j) = ModuleCat.of k (sinkSpace M p j) := rfl

theorem reflectSink_map_gen (hs : IsSink o p) (hf : IsFlipAt o o' p) (M : Diagram k o)
    {i j : Fin (n + 1)} (h : Arrow o' i j) (x : sinkSpace M p i) :
    (((reflectSink o' hs hf).obj M).map (gen h)).hom x =
      ⟨sinkLift M p i j x, sinkLift_mem M hs hf h x⟩ := by
  simp only [reflectSink, ofArrows_map_gen]
  rfl

/-! ### Reflected intervals -/

/-- The singleton interval `{p}`. -/
def singletonInterval (p : Fin (n + 1)) : FiniteInterval (n + 1) :=
  ⟨p.val, p.val + 1, Nat.lt_succ_self _, p.isLt⟩

/-- The interval obtained by reflecting at `p`: the endpoint next to `p` moves across `p`, and
the singleton `{p}` disappears. The rule is the same at sinks and at sources. -/
def reflectInterval (p : Fin (n + 1)) (J : FiniteInterval (n + 1)) :
    Option (FiniteInterval (n + 1)) :=
  if h : J.birth = p.val ∧ J.death = p.val + 1 then none else
    some
      { birth := if J.birth = p.val + 1 then p.val else if J.birth = p.val then p.val + 1
          else J.birth
        death := if J.death = p.val then p.val + 1 else if J.death = p.val + 1 then p.val
          else J.death
        birth_lt_death := by
          have := J.birth_lt_death
          have := J.death_le_size
          have := p.isLt
          split_ifs <;> omega
        death_le_size := by
          have := J.birth_lt_death
          have := J.death_le_size
          have := p.isLt
          split_ifs <;> omega }

theorem reflectInterval_eq_none_iff (p : Fin (n + 1)) (J : FiniteInterval (n + 1)) :
    reflectInterval p J = none ↔ J = singletonInterval p := by
  unfold reflectInterval singletonInterval
  constructor
  · intro h
    split_ifs at h with hJ
    cases J
    simp_all
  · rintro rfl
    simp

theorem reflectInterval_singleton (p : Fin (n + 1)) :
    reflectInterval p (singletonInterval p) = none :=
  (reflectInterval_eq_none_iff p _).mpr rfl

/-- Away from `p`, reflection does not change membership. -/
theorem alive_reflectInterval_of_ne {p : Fin (n + 1)} {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') {j : Fin (n + 1)} (hj : j ≠ p) :
    J'.alive j ↔ J.alive j := by
  unfold reflectInterval at hJ
  by_cases h : J.birth = p.val ∧ J.death = p.val + 1
  · simp [h] at hJ
  simp only [h, dite_false] at hJ
  cases hJ
  have hj' : j.val ≠ p.val := fun h' => hj (Fin.ext h')
  simp only [FiniteInterval.alive]
  have := J.birth_lt_death
  split_ifs <;> omega

/-- The reflected interval contains `p` exactly when the old one starts just after `p`, ends
just before `p`, or contains both neighbours of `p`. -/
theorem alive_reflectInterval_self {p : Fin (n + 1)} {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') :
    J'.alive p ↔ (J.birth = p.val + 1 ∨ J.death = p.val ∨
      (J.birth < p.val ∧ p.val + 1 < J.death)) := by
  unfold reflectInterval at hJ
  by_cases h : J.birth = p.val ∧ J.death = p.val + 1
  · simp [h] at hJ
  simp only [h, dite_false] at hJ
  cases hJ
  simp only [FiniteInterval.alive]
  have := J.birth_lt_death
  split_ifs <;> omega

/-- Reflecting twice at `p` returns every interval other than `{p}`. -/
theorem reflectInterval_reflectInterval {p : Fin (n + 1)} {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') : reflectInterval p J' = some J := by
  unfold reflectInterval at hJ
  by_cases h : J.birth = p.val ∧ J.death = p.val + 1
  · simp [h] at hJ
  simp only [h, dite_false] at hJ
  cases hJ
  have := J.birth_lt_death
  unfold reflectInterval
  simp only
  rw [dite_eq_right_of_eq_false (eq_false (by split_ifs <;> omega))]
  congr 1
  cases J
  simp only [FiniteInterval.mk.injEq] at h ⊢
  constructor <;> split_ifs <;> omega

/-! ### Sink reflection of interval diagrams -/

/-- At a sink every neighbour is an in-neighbour. -/
theorem IsSink.arrow_iff {o : Fin n → Bool} {p : Fin (n + 1)} (hs : IsSink o p)
    (l : Fin (n + 1)) : Arrow o l p ↔ (l.val + 1 = p.val ∨ p.val + 1 = l.val) := by
  constructor
  · intro h; exact h.adjacent
  · intro h
    rcases arrow_or_arrow o h with h' | h'
    · exact h'
    · exact absurd h' (hs l)

/-- The value of a fibre element of an interval diagram, as a linear map to the field. -/
def ivalL (J : FiniteInterval (n + 1)) (l : Fin (n + 1)) :
    (interval (k := k) o J).obj (vtx o l) →ₗ[k] k :=
  (J.fiber (k := k) l).subtype

/-- The value of a fibre element of an interval diagram. -/
abbrev ival {J : FiniteInterval (n + 1)} {l : Fin (n + 1)}
    (x : (interval (k := k) o J).obj (vtx o l)) : k :=
  ivalL J l x

/-- The value of an interval diagram map in the coefficient field. -/
theorem arr_interval_val (J : FiniteInterval (n + 1)) (i j : Fin (n + 1))
    (y : (interval (k := k) o J).obj (vtx o i)) :
    ival (arr (interval (k := k) o J) i j y) =
      if Arrow o i j ∧ J.alive i ∧ J.alive j then ival y else 0 := by
  by_cases h : Arrow o i j
  · rw [arr_of_arrow _ h]
    simp only [interval, ofArrows_map_gen]
    exact (fiberMap_val J i j y).trans (by simp [h]; rfl)
  · rw [arr_of_not_arrow _ h]
    simp [h]


theorem tot_interval_ext {J : FiniteInterval (n + 1)} {x y : Tot (interval (k := k) o J)}
    (h : ∀ l, ival (x l) = ival (y l)) : x = y :=
  funext fun l => Subtype.ext (h l)

@[simp] theorem ival_zero {J : FiniteInterval (n + 1)} {l : Fin (n + 1)} :
    ival (0 : (interval (k := k) o J).obj (vtx o l)) = 0 := rfl

@[simp] theorem ival_smul {J : FiniteInterval (n + 1)} {l : Fin (n + 1)} (c : k)
    (x : (interval (k := k) o J).obj (vtx o l)) : ival (c • x) = c * ival x := rfl

theorem ival_eq_zero {J : FiniteInterval (n + 1)} {l : Fin (n + 1)} (hl : ¬ J.alive l)
    (x : (interval (k := k) o J).obj (vtx o l)) : ival x = 0 :=
  fiber_val_eq_zero hl _

theorem ival_single {J : FiniteInterval (n + 1)} (j l : Fin (n + 1))
    (a : (interval (k := k) o J).obj (vtx o j)) :
    ival ((Pi.single j a : Tot (interval (k := k) o J)) l) = if l = j then ival a else 0 := by
  by_cases hl : l = j
  · subst hl; simp
  · simp [hl]

/-- A fibre element of an interval, as an element of the interval diagram. -/
def ofFiber (J : FiniteInterval (n + 1)) (l : Fin (n + 1)) :
    J.fiber (k := k) l →ₗ[k] (interval (k := k) o J).obj (vtx o l) :=
  LinearMap.id

@[simp] theorem ival_ofFiber (J : FiniteInterval (n + 1)) (l : Fin (n + 1))
    (y : J.fiber (k := k) l) : ival (ofFiber (o := o) J l y) = (y : k) := rfl

/-- The unit vector of an interval fibre: `1` inside the interval, `0` outside. -/
noncomputable def unitVec (J : FiniteInterval (n + 1)) (l : Fin (n + 1)) :
    (interval (k := k) o J).obj (vtx o l) :=
  ofFiber J l (if h : J.alive l then ⟨1, by simp [FiniteInterval.fiber, h]⟩ else 0)

theorem ival_unitVec (J : FiniteInterval (n + 1)) (l : Fin (n + 1)) :
    ival (unitVec (k := k) (o := o) J l) = if J.alive l then 1 else 0 := by
  unfold unitVec
  rw [ival_ofFiber]
  by_cases h : J.alive l <;> simp [h]

/-- The value of the signed incoming sum on an interval diagram. -/
theorem ival_sinkSum (J : FiniteInterval (n + 1)) (p : Fin (n + 1))
    (x : Tot (interval (k := k) o J)) :
    ival (sinkSum (interval (k := k) o J) p x) =
      ∑ l, sgn p l * (if Arrow o l p ∧ J.alive l ∧ J.alive p then ival (x l) else 0) := by
  rw [sinkSum_apply]
  dsimp only [ival]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, smul_eq_mul]
  exact congrArg _ (arr_interval_val J l p (x l))

theorem ival_injective {J : FiniteInterval (n + 1)} {l : Fin (n + 1)} :
    Function.Injective (ival (k := k) (o := o) (J := J) (l := l)) :=
  Subtype.val_injective

theorem sinkSpace_interval_ext {J : FiniteInterval (n + 1)} {p j : Fin (n + 1)}
    {x y : sinkSpace (interval (k := k) o J) p j}
    (h : ∀ l, ival (x.1 l) = ival (y.1 l)) : x = y :=
  Subtype.ext (tot_interval_ext h)

/-- The vector spanning the reflected interval at `j`: the unit vectors on the allowed
coordinates. -/
noncomputable def sinkVec (J : FiniteInterval (n + 1)) (p j : Fin (n + 1)) :
    Tot (interval (k := k) o J) :=
  fun l => if sinkSupp o p j l then unitVec J l else 0

theorem ival_sinkVec (J : FiniteInterval (n + 1)) (p j l : Fin (n + 1)) :
    ival (sinkVec (k := k) (o := o) J p j l) =
      if sinkSupp o p j l ∧ J.alive l then 1 else 0 := by
  unfold sinkVec
  by_cases h : sinkSupp o p j l
  · rw [if_pos h, ival_unitVec]; simp [h]
  · rw [if_neg h]; simp [h]

/-- The neighbour to the left of `p`. -/
def leftNbr (p : Fin (n + 1)) (hp : 0 < p.val) : Fin (n + 1) := ⟨p.val - 1, by omega⟩

/-- The neighbour to the right of `p`. -/
def rightNbr (p : Fin (n + 1)) (hp : p.val < n) : Fin (n + 1) := ⟨p.val + 1, by omega⟩

/-- The signed incoming sum of an interval diagram has at most two terms. -/
theorem ival_sinkSum_eq (hs : IsSink o p) (J : FiniteInterval (n + 1))
    (x : Tot (interval (k := k) o J)) :
    ival (sinkSum (interval (k := k) o J) p x) =
      (if h : 0 < p.val then
        (if J.alive (leftNbr p h) ∧ J.alive p then ival (x (leftNbr p h)) else 0) else 0) -
      (if h : p.val < n then
        (if J.alive (rightNbr p h) ∧ J.alive p then ival (x (rightNbr p h)) else 0) else 0) := by
  rw [ival_sinkSum]
  have hterm : ∀ l : Fin (n + 1),
      sgn (k := k) p l * (if Arrow o l p ∧ J.alive l ∧ J.alive p then ival (x l) else 0) =
        (if l.val + 1 = p.val ∧ J.alive l ∧ J.alive p then ival (x l) else 0) -
        (if p.val + 1 = l.val ∧ J.alive l ∧ J.alive p then ival (x l) else 0) := by
    intro l
    simp only [hs.arrow_iff l]
    unfold sgn
    by_cases h1 : l.val + 1 = p.val
    · have hlt : l < p := Fin.lt_def.mpr (by omega)
      have h2 : ¬ p.val + 1 = l.val := by omega
      simp [h1, h2, hlt]
    · by_cases h2 : p.val + 1 = l.val
      · have hlt : ¬ l < p := fun h => by rw [Fin.lt_def] at h; omega
        simp only [h1, h2, hlt, false_or, false_and, ite_false, true_and, zero_sub]
        split_ifs <;> simp
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_sub_distrib]
  congr 1
  · by_cases h : 0 < p.val
    · rw [dif_pos h, Fintype.sum_eq_single (leftNbr p h)]
      · have : (leftNbr p h).val + 1 = p.val := by simp only [leftNbr]; omega
        simp only [this, true_and]
      · intro l hl
        have : ¬ l.val + 1 = p.val := fun h' => hl (Fin.ext (by simp only [leftNbr]; omega))
        simp [this]
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun l _ => ?_
      have : ¬ l.val + 1 = p.val := by omega
      simp [this]
  · by_cases h : p.val < n
    · rw [dif_pos h, Fintype.sum_eq_single (rightNbr p h)]
      · have : p.val + 1 = (rightNbr p h).val := by simp only [rightNbr]
        simp only [this, true_and]
      · intro l hl
        have : ¬ p.val + 1 = l.val := fun h' => hl (Fin.ext (by simp only [rightNbr]; omega))
        simp [this]
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun l _ => ?_
      have : ¬ p.val + 1 = l.val := by have := l.isLt; have := p.isLt; omega
      simp [this]

theorem ival_sinkVec_self (hs : IsSink o p) (J : FiniteInterval (n + 1)) (l : Fin (n + 1)) :
    ival (sinkVec (k := k) (o := o) J p p l) =
      if (l.val + 1 = p.val ∨ p.val + 1 = l.val) ∧ J.alive l then 1 else 0 := by
  rw [ival_sinkVec]
  simp only [sinkSupp, ite_true, hs.arrow_iff l]

theorem ival_sinkVec_of_ne (J : FiniteInterval (n + 1)) {j : Fin (n + 1)} (hj : j ≠ p)
    (l : Fin (n + 1)) :
    ival (sinkVec (k := k) (o := o) J p j l) = if l = j ∧ J.alive l then 1 else 0 := by
  rw [ival_sinkVec]
  simp only [sinkSupp, hj, ite_false]

theorem leftNbr_eq {p l : Fin (n + 1)} (h : l.val + 1 = p.val) :
    l = leftNbr p (by omega) := Fin.ext (by simp only [leftNbr]; omega)

theorem rightNbr_eq {p l : Fin (n + 1)} (h : p.val + 1 = l.val) :
    l = rightNbr p (by have := l.isLt; omega) := Fin.ext (by simp only [rightNbr]; omega)

theorem sinkVec_mem (hs : IsSink o p) {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') {j : Fin (n + 1)} (hj : J'.alive j) :
    sinkVec (k := k) (o := o) J p j ∈ sinkSpace (interval (k := k) o J) p j := by
  rw [mem_sinkSpace]
  refine ⟨fun l hl => by simp [sinkVec, hl], fun hjp => ival_injective ?_⟩
  subst hjp
  have hJp := (alive_reflectInterval_self hJ).mp hj
  rw [ival_sinkSum_eq hs, ival_zero]
  have := J.birth_lt_death
  have := J.death_le_size
  have := j.isLt
  rcases hJp with hb | hd | ⟨hb, hd⟩
  · have hp : ¬ J.alive j := by simp only [FiniteInterval.alive]; omega
    simp [hp]
  · have hp : ¬ J.alive j := by simp only [FiniteInterval.alive]; omega
    simp [hp]
  · have h0 : 0 < j.val := by omega
    have hn : j.val < n := by omega
    have hp : J.alive j := by simp only [FiniteInterval.alive]; omega
    have hL : J.alive (leftNbr j h0) := by simp only [FiniteInterval.alive, leftNbr]; omega
    have hR : J.alive (rightNbr j hn) := by simp only [FiniteInterval.alive, rightNbr]; omega
    have hL' : (leftNbr j h0).val + 1 = j.val := by simp only [leftNbr]; omega
    have hR' : j.val + 1 = (rightNbr j hn).val := by simp only [rightNbr]
    rw [dif_pos h0, dif_pos hn, if_pos ⟨hL, hp⟩, if_pos ⟨hR, hp⟩, ival_sinkVec_self hs,
      ival_sinkVec_self hs, if_pos ⟨Or.inl hL', hL⟩, if_pos ⟨Or.inr hR', hR⟩, sub_self]

/-- The spanning vector of the reflected interval diagram at `j`. -/
noncomputable def sinkVecSub (hs : IsSink o p) {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') (j : Fin (n + 1)) :
    sinkSpace (interval (k := k) o J) p j := by
  classical
  exact if h : J'.alive j then ⟨sinkVec J p j, sinkVec_mem hs hJ h⟩ else 0

theorem ival_sinkVecSub (hs : IsSink o p) {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') (j l : Fin (n + 1)) :
    ival ((sinkVecSub (k := k) hs hJ j).1 l) =
      if J'.alive j then ival (sinkVec (k := k) (o := o) J p j l) else 0 := by
  unfold sinkVecSub
  by_cases h : J'.alive j
  · simp only [h, dite_true, ite_true]
  · simp only [h, dite_false, ite_false]; rfl

theorem ival_smul_sub {J : FiniteInterval (n + 1)} {j : Fin (n + 1)} (c : k)
    (y : sinkSpace (interval (k := k) o J) p j) (l : Fin (n + 1)) :
    ival ((c • y).1 l) = c * ival (y.1 l) := rfl

/-- Every element of a reflected interval space is a multiple of the spanning vector. -/
theorem sinkSpace_interval_span (hs : IsSink o p) {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') (j : Fin (n + 1))
    (x : sinkSpace (interval (k := k) o J) p j) :
    ∃ c : k, x = c • sinkVecSub hs hJ j := by
  obtain ⟨xx, hx⟩ := x
  rw [mem_sinkSpace] at hx
  obtain ⟨hsupp, hsum⟩ := hx
  have hdead : ∀ l, ¬ J.alive l → ival (xx l) = 0 := fun l hl => ival_eq_zero hl _
  have := J.birth_lt_death
  have := J.death_le_size
  by_cases hjp : j = p
  · subst hjp
    have hna : ∀ l : Fin (n + 1), ¬ (l.val + 1 = j.val ∨ j.val + 1 = l.val) → ival (xx l) = 0 := by
      intro l hl
      rw [hsupp l (by simpa [sinkSupp, hs.arrow_iff l] using hl), ival_zero]
    have hrel := congrArg ival (hsum rfl)
    rw [ival_sinkSum_eq hs, ival_zero] at hrel
    have hj := j.isLt
    by_cases hJ'j : J'.alive j
    · have hJp := (alive_reflectInterval_self hJ).mp hJ'j
      rcases hJp with hb | hd | ⟨hb, hd⟩
      · have hn : j.val < n := by omega
        refine ⟨ival (xx (rightNbr j hn)), sinkSpace_interval_ext fun l => ?_⟩
        rw [ival_smul_sub, ival_sinkVecSub, if_pos hJ'j, ival_sinkVec_self hs]
        by_cases hl1 : l.val + 1 = j.val
        · have hl : ¬ J.alive l := by simp only [FiniteInterval.alive]; omega
          rw [hdead l hl, if_neg (fun h => hl h.2), mul_zero]
        · by_cases hl2 : j.val + 1 = l.val
          · have hl : J.alive l := by simp only [FiniteInterval.alive]; omega
            rw [if_pos ⟨Or.inr hl2, hl⟩, mul_one, ← rightNbr_eq hl2]
          · rw [hna l (by omega), if_neg (by omega), mul_zero]
      · have h0 : 0 < j.val := by omega
        refine ⟨ival (xx (leftNbr j h0)), sinkSpace_interval_ext fun l => ?_⟩
        rw [ival_smul_sub, ival_sinkVecSub, if_pos hJ'j, ival_sinkVec_self hs]
        by_cases hl1 : l.val + 1 = j.val
        · have hl : J.alive l := by simp only [FiniteInterval.alive]; omega
          rw [if_pos ⟨Or.inl hl1, hl⟩, mul_one, ← leftNbr_eq hl1]
        · by_cases hl2 : j.val + 1 = l.val
          · have hl : ¬ J.alive l := by simp only [FiniteInterval.alive]; omega
            rw [hdead l hl, if_neg (fun h => hl h.2), mul_zero]
          · rw [hna l (by omega), if_neg (by omega), mul_zero]
      · have h0 : 0 < j.val := by omega
        have hn : j.val < n := by omega
        have hp : J.alive j := by simp only [FiniteInterval.alive]; omega
        have hL : J.alive (leftNbr j h0) := by simp only [FiniteInterval.alive, leftNbr]; omega
        have hR : J.alive (rightNbr j hn) := by
          simp only [FiniteInterval.alive, rightNbr]; omega
        rw [dif_pos h0, dif_pos hn, if_pos ⟨hL, hp⟩, if_pos ⟨hR, hp⟩, sub_eq_zero] at hrel
        refine ⟨ival (xx (leftNbr j h0)), sinkSpace_interval_ext fun l => ?_⟩
        rw [ival_smul_sub, ival_sinkVecSub, if_pos hJ'j, ival_sinkVec_self hs]
        by_cases hl1 : l.val + 1 = j.val
        · rw [if_pos ⟨Or.inl hl1, leftNbr_eq hl1 ▸ hL⟩, mul_one, ← leftNbr_eq hl1]
        · by_cases hl2 : j.val + 1 = l.val
          · rw [if_pos ⟨Or.inr hl2, rightNbr_eq hl2 ▸ hR⟩, mul_one, hrel, ← rightNbr_eq hl2]
          · rw [hna l (by omega), if_neg (by omega), mul_zero]
    · refine ⟨0, sinkSpace_interval_ext fun l => ?_⟩
      rw [ival_smul_sub, zero_mul]
      have hJp := mt (alive_reflectInterval_self hJ).mpr hJ'j
      change ival (xx l) = 0
      by_cases hl : J.alive l
      · by_cases hl1 : l.val + 1 = j.val
        · have h0 : 0 < j.val := by omega
          have hp : J.alive j := by simp only [FiniteInterval.alive] at hl ⊢; omega
          have hL : J.alive (leftNbr j h0) := leftNbr_eq hl1 ▸ hl
          rw [dif_pos h0, if_pos ⟨hL, hp⟩] at hrel
          by_cases hn : j.val < n
          · have hR : ¬ J.alive (rightNbr j hn) := by
              simp only [FiniteInterval.alive, rightNbr] at hl ⊢; omega
            rw [dif_pos hn, if_neg (fun h => hR h.1), sub_zero] at hrel
            rw [leftNbr_eq hl1]; exact hrel
          · rw [dif_neg hn, sub_zero] at hrel
            rw [leftNbr_eq hl1]; exact hrel
        · by_cases hl2 : j.val + 1 = l.val
          · have hn : j.val < n := by omega
            have hp : J.alive j := by simp only [FiniteInterval.alive] at hl ⊢; omega
            have hR : J.alive (rightNbr j hn) := rightNbr_eq hl2 ▸ hl
            rw [dif_pos hn, if_pos ⟨hR, hp⟩] at hrel
            by_cases h0 : 0 < j.val
            · have hL : ¬ J.alive (leftNbr j h0) := by
                simp only [FiniteInterval.alive, leftNbr] at hl ⊢; omega
              rw [dif_pos h0, if_neg (fun h => hL h.1), zero_sub, neg_eq_zero] at hrel
              rw [rightNbr_eq hl2]; exact hrel
            · rw [dif_neg h0, zero_sub, neg_eq_zero] at hrel
              rw [rightNbr_eq hl2]; exact hrel
          · exact hna l (by omega)
      · exact hdead l hl
  · refine ⟨ival (xx j), sinkSpace_interval_ext fun l => ?_⟩
    rw [ival_smul_sub, ival_sinkVecSub]
    change ival (xx l) = _
    have hsupp' : ∀ l, l ≠ j → ival (xx l) = 0 := by
      intro l hl
      rw [hsupp l (by simpa [sinkSupp, hjp] using hl), ival_zero]
    by_cases hJ'j : J'.alive j
    · have hJj := (alive_reflectInterval_of_ne hJ hjp).mp hJ'j
      rw [if_pos hJ'j, ival_sinkVec_of_ne J hjp]
      by_cases hl : l = j
      · subst hl; rw [if_pos ⟨rfl, hJj⟩, mul_one]
      · rw [hsupp' l hl, if_neg (fun h => hl h.1), mul_zero]
    · have hJj := mt (alive_reflectInterval_of_ne hJ hjp).mpr hJ'j
      rw [if_neg hJ'j, mul_zero]
      by_cases hl : l = j
      · subst hl; exact hdead l hJj
      · exact hsupp' l hl

theorem sinkVecSub_ne_zero (hs : IsSink o p) {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') {j : Fin (n + 1)} (hj : J'.alive j) :
    sinkVecSub (k := k) hs hJ j ≠ 0 := by
  have key : ∀ l, ival ((sinkVecSub (k := k) hs hJ j).1 l) = 1 →
      sinkVecSub (k := k) hs hJ j ≠ 0 := by
    intro l hl h0
    rw [h0] at hl
    exact zero_ne_one hl
  have := J.birth_lt_death
  have := J.death_le_size
  have hjl := j.isLt
  by_cases hjp : j = p
  · subst hjp
    rcases (alive_reflectInterval_self hJ).mp hj with hb | hd | ⟨hb, hd⟩
    · have hn : j.val < n := by omega
      refine key (rightNbr j hn) ?_
      rw [ival_sinkVecSub, if_pos hj, ival_sinkVec_self hs, if_pos]
      exact ⟨Or.inr rfl, by simp only [FiniteInterval.alive, rightNbr]; omega⟩
    · have h0 : 0 < j.val := by omega
      refine key (leftNbr j h0) ?_
      rw [ival_sinkVecSub, if_pos hj, ival_sinkVec_self hs, if_pos]
      exact ⟨Or.inl (by simp only [leftNbr]; omega),
        by simp only [FiniteInterval.alive, leftNbr]; omega⟩
    · have h0 : 0 < j.val := by omega
      refine key (leftNbr j h0) ?_
      rw [ival_sinkVecSub, if_pos hj, ival_sinkVec_self hs, if_pos]
      exact ⟨Or.inl (by simp only [leftNbr]; omega),
        by simp only [FiniteInterval.alive, leftNbr]; omega⟩
  · refine key j ?_
    rw [ival_sinkVecSub, if_pos hj, ival_sinkVec_of_ne J hjp, if_pos]
    exact ⟨rfl, (alive_reflectInterval_of_ne hJ hjp).mp hj⟩

theorem sinkVecSub_map (hs : IsSink o p) (hf : IsFlipAt o o' p) {J J' : FiniteInterval (n + 1)}
    (hJ : reflectInterval p J = some J') {i j : Fin (n + 1)} (h : Arrow o' i j)
    (hi : J'.alive i) (hj : J'.alive j) :
    (((reflectSink o' hs hf).obj (interval (k := k) o J)).map (gen h)).hom
      (sinkVecSub hs hJ i) = sinkVecSub hs hJ j := by
  rw [reflectSink_map_gen]
  have hjp : j ≠ p := by
    rintro rfl
    exact hf.isSource hs i h
  have hJj := (alive_reflectInterval_of_ne hJ hjp).mp hj
  apply sinkSpace_interval_ext
  intro l
  change ival (sinkLift (interval (k := k) o J) p i j (sinkVecSub hs hJ i).1 l) = _
  rw [ival_sinkVecSub hs hJ j l, if_pos hj, ival_sinkVec_of_ne J hjp]
  by_cases hip : i = p
  · rw [sinkLift_apply_self _ hip, ival_single, ival_sinkVecSub, if_pos hi]
    subst hip
    rw [ival_sinkVec_self hs]
    have hadj : j.val + 1 = i.val ∨ i.val + 1 = j.val := by
      rcases h.adjacent with h' | h' <;> omega
    by_cases hl : l = j
    · subst hl; simp [hadj, hJj]
    · simp [hl]
  · rw [sinkLift_apply_of_ne _ hip, ival_single]
    have hij : Arrow o i j := by
      have := (hf i j).mp h
      rwa [if_neg (by rintro (h' | h') <;> contradiction)] at this
    have hJi := (alive_reflectInterval_of_ne hJ hip).mp hi
    by_cases hl : l = j
    · subst hl
      rw [if_pos rfl, arr_interval_val, if_pos ⟨hij, hJi, hJj⟩, ival_sinkVecSub, if_pos hi,
        ival_sinkVec_of_ne J hip, if_pos ⟨rfl, hJi⟩, if_pos ⟨rfl, hJj⟩]
    · rw [if_neg hl, if_neg (fun h' => hl h'.1)]

/-- The sink reflection of an interval diagram other than `{p}` is the interval diagram of the
reflected interval. -/
noncomputable def reflectSinkIntervalIso (hs : IsSink o p) (hf : IsFlipAt o o' p)
    {J J' : FiniteInterval (n + 1)} (hJ : reflectInterval p J = some J') :
    interval (k := k) o' J' ≅ (reflectSink o' hs hf).obj (interval o J) :=
  intervalIso _ J' (fun j => sinkVecSub hs hJ j) (fun j x => sinkSpace_interval_span hs hJ j x)
    (fun _ hj => sinkVecSub_ne_zero hs hJ hj)
    (fun j hj => by unfold sinkVecSub; rw [dif_neg hj]; rfl)
    (fun h hi hj => sinkVecSub_map hs hf hJ h hi hj)

/-- The sink reflection kills the singleton interval at the sink. -/
theorem isZero_reflectSink_singleton (hs : IsSink o p) (hf : IsFlipAt o o' p) :
    IsZero ((reflectSink o' hs hf).obj (interval (k := k) o (singletonInterval p))) := by
  refine Functor.isZero _ fun X => ?_
  have : Subsingleton (sinkSpace (interval (k := k) o (singletonInterval p)) p X) := by
    refine ⟨fun x y => sinkSpace_interval_ext fun l => ?_⟩
    have hx : ∀ x : sinkSpace (interval (k := k) o (singletonInterval p)) p X,
        ival (x.1 l) = 0 := by
      intro x
      by_cases hl : l = p
      · subst hl
        have hsupp := ((mem_sinkSpace _ _ _ _).mp x.2).1 l
        have hns : ¬ sinkSupp o l X l := by
          unfold sinkSupp
          split_ifs with hX
          · exact fun h => h.ne rfl
          · exact fun h => hX h.symm
        rw [hsupp hns, ival_zero]
      · refine ival_eq_zero ?_ _
        simp only [FiniteInterval.alive, singletonInterval]
        exact fun h => hl (Fin.ext (by omega))
    rw [hx x, hx y]
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of k (sinkSpace _ p X))

/-- The sink reflection of an interval sum is the interval sum of the reflected intervals; the
copies of `{p}` disappear. -/
noncomputable def reflectSinkIntervalSumIso (hs : IsSink o p) (hf : IsFlipAt o o' p)
    (xs : List (FiniteInterval (n + 1))) :
    (reflectSink o' hs hf).obj (intervalSum (k := k) o xs) ≅
      intervalSum o' (xs.filterMap (reflectInterval p)) := by
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (reflectSink (k := k) o' hs hf)
  induction xs with
  | nil =>
    exact ((reflectSink o' hs hf).map_isZero (isZero_zero _)).iso (isZero_zero _)
  | cons J xs ih =>
    refine (reflectSink o' hs hf).mapBiprod _ _ ≪≫ ?_
    cases hJ : reflectInterval p J with
    | none =>
      rw [List.filterMap_cons_none hJ]
      have hzero : IsZero ((reflectSink o' hs hf).obj (interval (k := k) o J)) := by
        rw [(reflectInterval_eq_none_iff p J).mp hJ]
        exact isZero_reflectSink_singleton hs hf
      exact (isoZeroBiprod hzero).symm ≪≫ ih
    | some J' =>
      rw [List.filterMap_cons_some hJ]
      exact biprod.mapIso (reflectSinkIntervalIso hs hf hJ).symm ih

end TDA.Sheaf.AlternatingDiagram
