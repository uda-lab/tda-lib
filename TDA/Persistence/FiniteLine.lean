import TDA.Persistence.Basic
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Equioriented finite-line representations

The indexing quiver has one arrow between consecutive vertices. Its path category is
identified with the preorder category `Fin N`; adjacent linear maps therefore determine all
structure maps, and adjacent commuting squares determine natural transformations. The empty
line is included. This is specialized glue for mathlib's functor representation API.
-/

universe u w

namespace TDA.Persistence

open CategoryTheory

/-- Vertices of the equioriented finite line, separate from the preorder category on `Fin N`. -/
@[ext]
structure FiniteLine (N : ℕ) where
  index : Fin N

namespace FiniteLine

variable {N : ℕ}

/-- There is precisely one arrow `i → j` when `j` immediately follows `i`. -/
instance : Quiver (FiniteLine N) where
  Hom i j := PLift (i.index.val + 1 = j.index.val)

instance edgeSubsingleton (i j : FiniteLine N) : Subsingleton (i ⟶ j) :=
  inferInstanceAs (Subsingleton (PLift (i.index.val + 1 = j.index.val)))

/-- Every path moves weakly forward along the finite line. -/
theorem le_of_path {i j : FiniteLine N} (p : Quiver.Path i j) : i.index ≤ j.index := by
  induction p with
  | nil => exact le_rfl
  | @cons j k p e ih =>
    have he := e.down
    change i.index.val ≤ k.index.val
    have hi : i.index.val ≤ j.index.val := ih
    omega

/-- A finite line has at most one path between any two vertices. -/
instance pathSubsingleton (i j : FiniteLine N) : Subsingleton (Quiver.Path i j) where
  allEq p q := by
    induction p with
    | nil =>
      cases q with
      | nil => rfl
      | @cons j _ q e =>
        have hq := le_of_path q
        have he := e.down
        change i.index.val ≤ j.index.val at hq
        omega
    | @cons j k p e ih =>
      cases q with
      | nil =>
        have hp := le_of_path p
        have he := e.down
        change i.index.val ≤ j.index.val at hp
        omega
      | @cons l _ q e' =>
        have hjl : j = l := by
          apply FiniteLine.ext
          apply Fin.ext
          have he := e.down
          have he' := e'.down
          omega
        subst l
        rw [ih q]
        congr 1
        exact Subsingleton.elim _ _

instance pathCategorySubsingleton (i j : Paths (FiniteLine N)) : Subsingleton (i ⟶ j) :=
  inferInstanceAs (Subsingleton (Quiver.Path (show FiniteLine N from i) (show FiniteLine N from j)))

private theorem nonempty_path (i j : FiniteLine N) (h : i.index ≤ j.index) :
    Nonempty (Quiver.Path i j) := by
  have aux : ∀ n, ∀ j : FiniteLine N, j.index.val = n → i.index ≤ j.index →
      Nonempty (Quiver.Path i j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj hij
      by_cases heq : i = j
      · subst j
        exact ⟨.nil⟩
      · have hlt : i.index.val < j.index.val := by
          have hne : i.index.val ≠ j.index.val := by
            intro he
            exact heq (FiniteLine.ext (Fin.ext he))
          change i.index.val ≤ j.index.val at hij
          omega
        let k : FiniteLine N := ⟨⟨j.index.val - 1, by omega⟩⟩
        have hkn : k.index.val < n := by dsimp [k]; omega
        have hik : i.index ≤ k.index := by change i.index.val ≤ j.index.val - 1; omega
        obtain ⟨p⟩ := ih k.index.val hkn k rfl hik
        exact ⟨p.cons ⟨by dsimp [k]; omega⟩⟩
  exact aux j.index.val j rfl h

/-- The unique chronological path associated to an inequality. -/
noncomputable def path {i j : FiniteLine N} (h : i.index ≤ j.index) : Quiver.Path i j :=
  Classical.choice (nonempty_path i j h)

/-- The canonical self path is the empty path. -/
@[simp]
theorem path_self (i : FiniteLine N) (h : i.index ≤ i.index) :
    path h = (Quiver.Path.nil : Quiver.Path i i) := Subsingleton.elim _ _

/-- On consecutive vertices the canonical path is the single quiver arrow. -/
theorem path_adjacent {i j : FiniteLine N} (h : i.index.val + 1 = j.index.val) :
    path (show i.index ≤ j.index by change i.index.val ≤ j.index.val; omega) =
      Quiver.Hom.toPath (⟨h⟩ : i ⟶ j) := Subsingleton.elim _ _

/-- Concatenating chronological paths gives the chronological path for the total inequality. -/
theorem path_comp {i j k : FiniteLine N} (hij : i.index ≤ j.index)
    (hjk : j.index ≤ k.index) :
    (path hij).comp (path hjk) = path (hij.trans hjk) := Subsingleton.elim _ _

/-- Collapsing a path remembers its endpoint inequality. -/
def toFin : Paths (FiniteLine N) ⥤ Fin N where
  obj i := i.index
  map p := homOfLE (le_of_path p)

/-- An inequality expands to its unique chronological path. -/
noncomputable def fromFin : Fin N ⥤ Paths (FiniteLine N) where
  obj i := ⟨i⟩
  map f := path (leOfHom f)
  map_id _ := (pathSubsingleton _ _).elim _ _
  map_comp _ _ := (pathSubsingleton _ _).elim _ _

/-- The path category of a finite line is the preorder category, including at `N = 0`. -/
noncomputable def pathEquivalence (N : ℕ) : Paths (FiniteLine N) ≌ Fin N where
  functor := toFin
  inverse := fromFin
  unitIso := NatIso.ofComponents (fun i => eqToIso (by cases i; rfl))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

variable {R : Type u} [Ring R]

/-- Representations of the finite-line path category are precisely finite persistence modules.
Objects are precomposed with `fromFin`, and morphisms are whiskered along that functor. -/
noncomputable def representationEquivalence (R : Type u) [Ring R] (N : ℕ) :
    (Paths (FiniteLine N) ⥤ ModuleCat.{w} R) ≌ PModule R (Fin N) :=
  (pathEquivalence N).congrLeft

/-- Extend adjacent linear maps to the unique persistence module on the finite line. -/
noncomputable def moduleOfAdjacent (V : Fin N → ModuleCat.{w} R)
    (step : ∀ (i j : Fin N), i.val + 1 = j.val → (V i ⟶ V j)) : PModule R (Fin N) :=
  fromFin ⋙ Paths.lift (⟨fun i => V i.index, fun {i j} e => step i.index j.index e.down⟩ :
    FiniteLine N ⥤q ModuleCat.{w} R)

/-- The adjacent-map construction has exactly the supplied fibers. -/
@[simp]
theorem moduleOfAdjacent_obj (V : Fin N → ModuleCat.{w} R)
    (step : ∀ (i j : Fin N), i.val + 1 = j.val → (V i ⟶ V j)) (i : Fin N) :
    (moduleOfAdjacent V step).obj i = V i := rfl

/-- On consecutive vertices the constructed structure map is the supplied map. -/
@[simp]
theorem structureMap_moduleOfAdjacent_adjacent (V : Fin N → ModuleCat.{w} R)
    (step : ∀ (i j : Fin N), i.val + 1 = j.val → (V i ⟶ V j))
    {i j : Fin N} (h : i.val + 1 = j.val) :
    structureMap (moduleOfAdjacent V step) (show i ≤ j by omega) = step i j h := by
  change (Paths.lift _).map
    (path (i := ⟨i⟩) (j := ⟨j⟩) (show i ≤ j by omega)) = _
  rw [path_adjacent (i := ⟨i⟩) (j := ⟨j⟩) h]
  exact Paths.lift_toPath _ _

/-- Adjacent squares imply naturality for every structure map. -/
theorem naturality_of_adjacent {M W : PModule.{u,0,w} R (Fin N)}
    (α : ∀ i, M.obj i ⟶ W.obj i)
    (hα : ∀ (i j : Fin N) (h : i.val + 1 = j.val),
      structureMap M (show i ≤ j by omega) ≫ α j =
        α i ≫ structureMap W (show i ≤ j by omega))
    {i j : Fin N} (h : i ≤ j) :
    structureMap M h ≫ α j = α i ≫ structureMap W h := by
  have hp : ∀ {a b : FiniteLine N} (p : Quiver.Path a b),
      structureMap M (le_of_path p) ≫ α b.index =
        α a.index ≫ structureMap W (le_of_path p) := by
    intro a b p
    induction p with
    | nil => simp
    | @cons b c p e ih =>
      have hbc : b.index ≤ c.index := by
        have he := e.down
        change b.index.val ≤ c.index.val
        omega
      have hs := hα b.index c.index e.down
      have hm := structureMap_comp M (le_of_path p) hbc
      have hw := structureMap_comp W (le_of_path p) hbc
      rw [← hm, ← hw, Category.assoc, hs, ← Category.assoc, ih, Category.assoc]
  exact hp (path h)

/-- Construct a morphism of arbitrary finite persistence modules using adjacent squares only. -/
noncomputable def homMk {M W : PModule.{u,0,w} R (Fin N)}
    (α : ∀ i, M.obj i ⟶ W.obj i)
    (hα : ∀ (i j : Fin N) (h : i.val + 1 = j.val),
      structureMap M (show i ≤ j by omega) ≫ α j =
        α i ≫ structureMap W (show i ≤ j by omega)) : M ⟶ W where
  app := α
  naturality {_ _} f := naturality_of_adjacent α hα (leOfHom f)

/-- The morphism constructor retains the supplied stage maps. -/
@[simp]
theorem homMk_app {M W : PModule.{u,0,w} R (Fin N)} (α) (hα) (i : Fin N) :
    (homMk (M := M) (W := W) α hα).app i = α i := rfl

/-- Construct a morphism directly from adjacent-map input. -/
noncomputable def homOfAdjacent (V W : Fin N → ModuleCat.{w} R)
    (step : ∀ (i j : Fin N), i.val + 1 = j.val → (V i ⟶ V j))
    (step' : ∀ (i j : Fin N), i.val + 1 = j.val → (W i ⟶ W j))
    (α : ∀ i, V i ⟶ W i)
    (hα : ∀ (i j : Fin N) (h : i.val + 1 = j.val),
      step i j h ≫ α j = α i ≫ step' i j h) :
    moduleOfAdjacent V step ⟶ moduleOfAdjacent W step' :=
  homMk α (by
    intro i j h
    erw [structureMap_moduleOfAdjacent_adjacent V step h,
      structureMap_moduleOfAdjacent_adjacent W step' h]
    exact hα i j h)

/-- The morphism on adjacent input retains the supplied components. -/
@[simp]
theorem homOfAdjacent_app (V W : Fin N → ModuleCat.{w} R) (step step') (α) (hα)
    (i : Fin N) : (homOfAdjacent V W step step' α hα).app i = α i := rfl

/-- Fiber isomorphisms intertwining adjacent maps give a genuine natural isomorphism. -/
noncomputable def isoOfAdjacent {M W : PModule.{u,0,w} R (Fin N)}
    (e : ∀ i, M.obj i ≅ W.obj i)
    (he : ∀ (i j : Fin N) (h : i.val + 1 = j.val),
      structureMap M (show i ≤ j by omega) ≫ (e j).hom =
        (e i).hom ≫ structureMap W (show i ≤ j by omega)) : M ≅ W :=
  NatIso.ofComponents e (fun f => naturality_of_adjacent (fun i => (e i).hom) he (leOfHom f))

/-- The adjacent-square isomorphism has the supplied forward components. -/
@[simp]
theorem isoOfAdjacent_hom_app {M W : PModule.{u,0,w} R (Fin N)} (e) (he) (i : Fin N) :
    (isoOfAdjacent (M := M) (W := W) e he).hom.app i = (e i).hom := rfl

/-- Its inverse has the supplied inverse components. -/
@[simp]
theorem isoOfAdjacent_inv_app {M W : PModule.{u,0,w} R (Fin N)} (e) (he) (i : Fin N) :
    (isoOfAdjacent (M := M) (W := W) e he).inv.app i = (e i).inv := rfl

/-- Actual structure maps are evaluated by lifting the unique chronological path. -/
theorem structureMap_moduleOfAdjacent_path (V : Fin N → ModuleCat.{w} R)
    (step : ∀ (i j : Fin N), i.val + 1 = j.val → (V i ⟶ V j))
    {i j : Fin N} (h : i ≤ j) :
    structureMap (moduleOfAdjacent V step) h =
      (Paths.lift (⟨fun a => V a.index,
        fun {a b} e => step a.index b.index e.down⟩ :
          FiniteLine N ⥤q ModuleCat.{w} R)).map (path h) := rfl

/-- Chronological recursion: append the last adjacent map after the preceding structure map.
Together with the identity case, this specifies every structure map. -/
theorem structureMap_moduleOfAdjacent_last (V : Fin N → ModuleCat.{w} R)
    (step : ∀ (i j : Fin N), i.val + 1 = j.val → (V i ⟶ V j))
    {i j k : Fin N} (hij : i ≤ j) (hjk : j.val + 1 = k.val) :
    structureMap (moduleOfAdjacent V step) (show i ≤ k by omega) =
      structureMap (moduleOfAdjacent V step) hij ≫ step j k hjk := by
  have hc := structureMap_comp (moduleOfAdjacent V step) hij (show j ≤ k by omega)
  erw [structureMap_moduleOfAdjacent_adjacent V step hjk] at hc
  exact hc.symm

/-- Extract the adjacent maps of a persistence module. -/
def adjacentMap (M : PModule.{u,0,w} R (Fin N)) (i j : Fin N)
    (h : i.val + 1 = j.val) : M.obj i ⟶ M.obj j :=
  structureMap M (show i ≤ j by omega)

/-- Reconstructing a module from its adjacent maps gives a genuine natural isomorphism. -/
noncomputable def adjacentRecovery (M : PModule.{u,0,w} R (Fin N)) :
    moduleOfAdjacent M.obj (adjacentMap M) ≅ M :=
  isoOfAdjacent (fun _ => Iso.refl _) (by
    intro i j h
    erw [structureMap_moduleOfAdjacent_adjacent M.obj (adjacentMap M) h]
    exact Category.comp_id _)

/-- The recovery isomorphism is the identity on each supplied fiber. -/
@[simp]
theorem adjacentRecovery_hom_app (M : PModule.{u,0,w} R (Fin N)) (i : Fin N) :
    (adjacentRecovery M).hom.app i = 𝟙 (M.obj i) := rfl

/-- The inverse recovery isomorphism is also the identity on each fiber. -/
@[simp]
theorem adjacentRecovery_inv_app (M : PModule.{u,0,w} R (Fin N)) (i : Fin N) :
    (adjacentRecovery M).inv.app i = 𝟙 (M.obj i) := rfl

/-- Reconstruction recovers every original structure map, including nonadjacent maps. -/
@[simp]
theorem structureMap_adjacentRecovery (M : PModule.{u,0,w} R (Fin N))
    {i j : Fin N} (h : i ≤ j) :
    structureMap (moduleOfAdjacent M.obj (adjacentMap M)) h = structureMap M h := by
  have hn := (adjacentRecovery M).hom.naturality (homOfLE h)
  change structureMap (moduleOfAdjacent M.obj (adjacentMap M)) h ≫ 𝟙 _ =
    𝟙 _ ≫ structureMap M h at hn
  exact (Category.comp_id _).symm.trans (hn.trans (Category.id_comp _))

/-- Recovery is compatible with actual morphisms, not only the module fibers. -/
theorem adjacentRecovery_naturality {M W : PModule.{u,0,w} R (Fin N)} (α : M ⟶ W) :
    homOfAdjacent M.obj W.obj (adjacentMap M) (adjacentMap W) α.app
      (fun _ _ h => α.naturality (homOfLE (show _ ≤ _ by omega))) ≫
        (adjacentRecovery W).hom = (adjacentRecovery M).hom ≫ α := by
  apply NatTrans.ext
  funext i
  change α.app i ≫ 𝟙 _ = 𝟙 _ ≫ α.app i
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The indexing equivalence evaluates to the original vertex. -/
@[simp]
theorem pathEquivalence_functor_obj (i : Paths (FiniteLine N)) :
    (pathEquivalence N).functor.obj i = i.index := rfl

/-- The inverse indexing equivalence uses the corresponding line vertex. -/
@[simp]
theorem pathEquivalence_inverse_obj (i : Fin N) :
    (pathEquivalence N).inverse.obj i = (⟨i⟩ : FiniteLine N) := rfl

/-- The representation equivalence preserves the value at each vertex. -/
@[simp]
theorem representationEquivalence_obj_obj (F : Paths (FiniteLine N) ⥤ ModuleCat.{w} R)
    (i : Fin N) :
    ((representationEquivalence R N).functor.obj F).obj i = F.obj ⟨i⟩ := rfl

/-- The forward representation equivalence evaluates a structure map on the unique path. -/
@[simp]
theorem representationEquivalence_structureMap
    (F : Paths (FiniteLine N) ⥤ ModuleCat.{w} R) {i j : Fin N} (h : i ≤ j) :
    structureMap ((representationEquivalence R N).functor.obj F) h = F.map (path h) := rfl

/-- The representation equivalence carries the actual components of natural transformations. -/
@[simp]
theorem representationEquivalence_map_app
    {F G : Paths (FiniteLine N) ⥤ ModuleCat.{w} R} (α : F ⟶ G) (i : Fin N) :
    ((representationEquivalence R N).functor.map α).app i = α.app ⟨i⟩ := rfl

/-- In the reverse direction, paths act by the original module's structure maps. -/
@[simp]
theorem representationEquivalence_inverse_map (M : PModule.{u,0,w} R (Fin N))
    {i j : Paths (FiniteLine N)} (p : i ⟶ j) :
    ((representationEquivalence R N).inverse.obj M).map p =
      structureMap M (le_of_path p) := rfl

/-- The inverse equivalence also preserves the components of natural transformations. -/
@[simp]
theorem representationEquivalence_inverse_map_app
    {M W : PModule.{u,0,w} R (Fin N)} (α : M ⟶ W) (i : Paths (FiniteLine N)) :
    ((representationEquivalence R N).inverse.map α).app i = α.app i.index := rfl

/-- The unit of the representation equivalence is the identity at every vertex. -/
@[simp]
theorem representationEquivalence_unitIso_hom_app
    (F : Paths (FiniteLine N) ⥤ ModuleCat.{w} R) (i : Paths (FiniteLine N)) :
    ((representationEquivalence R N).unitIso.hom.app F).app i = 𝟙 (F.obj i) := by
  change (𝟙 _ ≫ F.map _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  have he : (pathEquivalence N).unitIso.hom.app i = 𝟙 i := Subsingleton.elim _ _
  change F.map ((pathEquivalence N).unitIso.hom.app i) = _
  erw [he, F.map_id]
  rfl

/-- The counit of the representation equivalence is the identity on each module fiber. -/
@[simp]
theorem representationEquivalence_counitIso_hom_app
    (M : PModule.{u,0,w} R (Fin N)) (i : Fin N) :
    ((representationEquivalence R N).counitIso.hom.app M).app i = 𝟙 (M.obj i) := by
  change (𝟙 _ ≫ M.map _ ≫ 𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]
  have he : (pathEquivalence N).counitIso.hom.app i = 𝟙 i := Subsingleton.elim _ _
  rw [he, M.map_id]

/-- The forward equivalence preserves identity morphisms. -/
@[simp]
theorem representationEquivalence_map_id (F : Paths (FiniteLine N) ⥤ ModuleCat.{w} R) :
    (representationEquivalence R N).functor.map (𝟙 F) =
      𝟙 ((representationEquivalence R N).functor.obj F) :=
  (representationEquivalence R N).functor.map_id F

/-- The forward equivalence preserves composition of actual natural transformations. -/
@[simp]
theorem representationEquivalence_map_comp
    {F G H : Paths (FiniteLine N) ⥤ ModuleCat.{w} R} (α : F ⟶ G) (β : G ⟶ H) :
    (representationEquivalence R N).functor.map (α ≫ β) =
      (representationEquivalence R N).functor.map α ≫
        (representationEquivalence R N).functor.map β :=
  (representationEquivalence R N).functor.map_comp α β

end FiniteLine
end TDA.Persistence
