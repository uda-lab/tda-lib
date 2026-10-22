import TDA.Mapper.CoverComponents
import TDA.Topology.Nerve
import TDA.Reeb.ComponentsGluing

/-!
# Categorical Mapper intersection data

The categorical Mapper retains path components over every nonempty intersection of
cover members. Its face maps are induced by the inclusions of those intersections.
For a test interval, the selected simplices are precisely those whose cover intersection
meets that interval. Their component maps form a cocone into the path components of the
cover saturation.
-/

open Set CategoryTheory CategoryTheory.Limits

universe u v

namespace TDA.Mapper

open TDA.Reeb TDA.Reeb.OpenInterval

variable {ι : Type v}

/-- A nonempty simplex of the target-cover nerve, retaining its original labels. -/
abbrev CoverSimplex (U : ι → OpenInterval) :=
  {s : Finset ι // s ∈ TDA.Topology.nerve (fun i => (U i : Set ℝ))}

/-- The open intersection belonging to a cover simplex. -/
def coverIntersection (U : ι → OpenInterval) (s : CoverSimplex U) :
    TopologicalSpace.Opens ℝ :=
  ⨅ i : s.val, toOpens (U i.val)

@[simp] theorem mem_coverIntersection (U : ι → OpenInterval) (s : CoverSimplex U) (x : ℝ) :
    x ∈ coverIntersection U s ↔ ∀ i ∈ s.val, x ∈ U i := by
  change x ∈ ((⨅ i : s.val, toOpens (U i.val) : TopologicalSpace.Opens ℝ) : Set ℝ) ↔ _
  rw [TopologicalSpace.Opens.coe_iInf]
  simp only [Set.mem_iInter]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i.val i.property⟩


/-- A finite intersection of cover intervals, regarded as an open interval. -/
def coverIntersectionInterval (U : ι → OpenInterval) (s : CoverSimplex U) : OpenInterval where
  carrier := coverIntersection U s
  isOpen' := (coverIntersection U s).isOpen
  ordConnected' := by
    change Set.OrdConnected
      ((⨅ i : s.val, toOpens (U i.val) : TopologicalSpace.Opens ℝ) : Set ℝ)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.ordConnected_iInter (fun i => (U i.val).ordConnected)

/-- The interval presentation has exactly the original open intersection. -/
@[simp] theorem toOpens_coverIntersectionInterval (U : ι → OpenInterval) (s : CoverSimplex U) :
    toOpens (coverIntersectionInterval U s) = coverIntersection U s := rfl

/-- Cover-intersection inclusions reverse the face order. -/
theorem coverIntersection_antitone (U : ι → OpenInterval) {s t : CoverSimplex U}
    (h : s ≤ t) : coverIntersection U t ≤ coverIntersection U s := by
  intro x hx
  exact (mem_coverIntersection U s x).mpr fun i hi =>
    (mem_coverIntersection U t x).mp hx i (h hi)

/-- The contravariant intersection functor on the cover nerve. -/
def coverIntersectionFunctor (U : ι → OpenInterval) :
    (CoverSimplex U)ᵒᵈ ⥤ TopologicalSpace.Opens ℝ where
  obj := coverIntersection U
  map h := homOfLE (coverIntersection_antitone U (leOfHom h))

variable {X : Type u} [TopologicalSpace X]

/-- Categorical Mapper: all intersection-component sets and their incidence maps. -/
def categoricalMapperData (f : C(X, ℝ)) (U : ι → OpenInterval) :
    (CoverSimplex U)ᵒᵈ ⥤ Type u :=
  coverIntersectionFunctor U ⋙ componentFunctor f

/-- The subcategory of simplices whose intersections meet a test interval. -/
abbrev ActiveCoverSimplex (U : ι → OpenInterval) (I : OpenInterval) :=
  {s : CoverSimplex U // ((coverIntersection U s : Set ℝ) ∩ I).Nonempty}

/-- Inclusion of the selected face subcategory. -/
def activeCoverSimplexInclusion (U : ι → OpenInterval) (I : OpenInterval) :
    (ActiveCoverSimplex U I)ᵒᵈ ⥤ (CoverSimplex U)ᵒᵈ where
  obj := Subtype.val
  map h := homOfLE (leOfHom h)

/-- The categorical assembly diagram over one test interval. -/
def categoricalMapperDiagram (f : C(X, ℝ)) (U : ι → OpenInterval) (I : OpenInterval) :
    (ActiveCoverSimplex U I)ᵒᵈ ⥤ Type u :=
  activeCoverSimplexInclusion U I ⋙ categoricalMapperData f U


/-- Enlarging a test interval includes its selected simplices into the new selected category. -/
def activeCoverSimplexMap (U : ι → OpenInterval) {I J : OpenInterval} (hIJ : I ≤ J) :
    (ActiveCoverSimplex U I)ᵒᵈ ⥤ (ActiveCoverSimplex U J)ᵒᵈ where
  obj s := ⟨s.val, by
    obtain ⟨y, hyU, hyI⟩ := s.property
    exact ⟨y, hyU, hIJ hyI⟩⟩
  map h := homOfLE (leOfHom h)

/-- Each selected intersection lies in the union of the members meeting the test interval. -/
theorem coverIntersection_le_saturation (U : ι → OpenInterval) (I : OpenInterval)
    (s : ActiveCoverSimplex U I) : coverIntersection U s.val ≤ coverSaturation U I := by
  intro x hx
  obtain ⟨i, hi⟩ := s.val.property.1
  obtain ⟨y, hyU, hyI⟩ := s.property
  exact mem_coverSaturation.mpr ⟨i, (mem_coverIntersection U s.val x).mp hx i hi,
    y, (mem_coverIntersection U s.val y).mp hyU i hi, hyI⟩

/-- The component-inclusion cocone from categorical Mapper data to the saturated set. -/
def categoricalMapperCocone (f : C(X, ℝ)) (U : ι → OpenInterval) (I : OpenInterval) :
    Cocone (categoricalMapperDiagram f U I) where
  pt := (coverComponents f U).obj I
  ι :=
    { app := fun s => (componentFunctor f).map
        (homOfLE (coverIntersection_le_saturation U I s))
      naturality := fun s t h => by
        ext c
        induction c using ZerothHomotopy.rec with
        | mk x => rfl }


/-- The interval map on the assembly commutes with every selected intersection component map.
Together with `categoricalMapperIsColimit`, this characterizes the map induced by `P_K`. -/
theorem categoricalMapperCocone_map (f : C(X, ℝ)) (U : ι → OpenInterval)
    {I J : OpenInterval} (hIJ : I ≤ J) (s : ActiveCoverSimplex U I) :
    (categoricalMapperCocone f U I).ι.app s ≫ (coverComponents f U).map (homOfLE hIJ) =
      (categoricalMapperCocone f U J).ι.app ((activeCoverSimplexMap U hIJ).obj s) := by
  ext c
  induction c using ZerothHomotopy.rec with
  | mk x => rfl

/-- Three real intervals with pairwise nonempty intersections have a common point. -/
theorem intervalTripleIntersection_nonempty (I J K : OpenInterval)
    (hIJ : ((I : Set ℝ) ∩ J).Nonempty) (hIK : ((I : Set ℝ) ∩ K).Nonempty)
    (hJK : ((J : Set ℝ) ∩ K).Nonempty) :
    ∃ x, x ∈ I ∧ x ∈ J ∧ x ∈ K := by
  obtain ⟨z, hzI, hzJ⟩ := hIJ
  obtain ⟨x, hxI, hxK⟩ := hIK
  obtain ⟨y, hyJ, hyK⟩ := hJK
  rcases le_total x y with hxy | hyx
  · rcases le_total z x with hzx | hxz
    · exact ⟨x, hxI, J.ordConnected.out hzJ hyJ ⟨hzx, hxy⟩, hxK⟩
    · rcases le_total z y with hzy | hyz
      · exact ⟨z, hzI, hzJ, K.ordConnected.out hxK hyK ⟨hxz, hzy⟩⟩
      · exact ⟨y, I.ordConnected.out hxI hzI ⟨hxy, hyz⟩, hyJ, hyK⟩
  · rcases le_total z y with hzy | hyz
    · exact ⟨y, I.ordConnected.out hzI hxI ⟨hzy, hyx⟩, hyJ, hyK⟩
    · rcases le_total z x with hzx | hxz
      · exact ⟨z, hzI, hzJ, K.ordConnected.out hyK hxK ⟨hyz, hzx⟩⟩
      · exact ⟨x, hxI, J.ordConnected.out hyJ hzJ ⟨hyx, hxz⟩, hxK⟩

noncomputable section

local instance categoricalMapperDecidableEq : DecidableEq ι := Classical.decEq ι

/-- The selected singleton simplex corresponding to an active cover member. -/
def activeCoverSingleton (U : ι → OpenInterval) (I : OpenInterval)
    (i : ActiveCoverMember U I) : ActiveCoverSimplex U I := by
  refine ⟨⟨{i.val}, ?_⟩, ?_⟩
  · obtain ⟨y, hyU, hyI⟩ := i.property
    exact ⟨Finset.singleton_nonempty _, y, fun j hj =>
      (Finset.mem_singleton.mp hj) ▸ hyU⟩
  · obtain ⟨y, hyU, hyI⟩ := i.property
    exact ⟨y, (mem_coverIntersection U _ y).mpr (fun j hj =>
      (Finset.mem_singleton.mp hj) ▸ hyU), hyI⟩

/-- The singleton intersection agrees with the original labelled member. -/
theorem coverIntersection_activeCoverSingleton (U : ι → OpenInterval) (I : OpenInterval)
    (i : ActiveCoverMember U I) :
    coverIntersection U (activeCoverSingleton U I i).val = toOpens (U i.val) := by
  ext x
  constructor
  · intro hx
    exact (mem_coverIntersection U (activeCoverSingleton U I i).val x).mp hx i.val
      (Finset.mem_singleton_self _)
  · intro hx
    exact (mem_coverIntersection U (activeCoverSingleton U I i).val x).mpr
      (fun j hj => (Finset.mem_singleton.mp hj) ▸ hx)

/-- Evaluation of a categorical cocone on the original component set of a selected member. -/
def categoricalMapperMemberMap (f : C(X, ℝ)) (U : ι → OpenInterval) (I : OpenInterval)
    (c : Cocone (categoricalMapperDiagram f U I)) (i : ActiveCoverMember U I) :
    (intervalComponents f).obj (U i.val) → c.pt :=
  fun x => c.ι.app (activeCoverSingleton U I i)
    ((componentFunctor f).map
      (homOfLE (coverIntersection_activeCoverSingleton U I i).ge) x)


/-- A cocone's singleton value agrees with its value on every incident selected simplex. -/
theorem categoricalMapperMemberMap_face (f : C(X, ℝ)) (U : ι → OpenInterval)
    (I : OpenInterval) (c : Cocone (categoricalMapperDiagram f U I))
    (s : ActiveCoverSimplex U I) (i : ActiveCoverMember U I) (hi : i.val ∈ s.val.val)
    (e : (componentFunctor f).obj (coverIntersection U s.val)) :
    categoricalMapperMemberMap f U I c i
      ((componentFunctor f).map (homOfLE (fun x hx =>
        (mem_coverIntersection U s.val x).mp hx i.val hi)) e) = c.ι.app s e := by
  let h : OrderDual.toDual s ⟶ OrderDual.toDual (activeCoverSingleton U I i) :=
    homOfLE (Finset.singleton_subset_iff.mpr hi)
  have hw := c.w_apply h e
  induction e using ZerothHomotopy.rec with
  | mk x => exact hw

/-- The saturated component set is the colimit of the categorical Mapper diagram. -/
def categoricalMapperIsColimit (f : C(X, ℝ)) (U : ι → OpenInterval) (I : OpenInterval) :
    IsColimit (categoricalMapperCocone f U I) := by
  classical
  have hcov : coverSaturation U I ≤ ⨆ i : ActiveCoverMember U I, toOpens (U i.val) := by
    intro x hx
    obtain ⟨i, hxi, y, hyU, hyI⟩ := mem_coverSaturation.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, y, hyU, hyI⟩, hxi⟩
  have compatible (c : Cocone (categoricalMapperDiagram f U I))
      (i j : ActiveCoverMember U I)
      (e : (componentFunctor f).obj (toOpens (U i.val) ⊓ toOpens (U j.val))) :
      categoricalMapperMemberMap f U I c i
        ((componentFunctor f).map (homOfLE inf_le_left) e) =
      categoricalMapperMemberMap f U I c j
        ((componentFunctor f).map (homOfLE inf_le_right) e) := by
    induction e using ZerothHomotopy.rec with
    | mk x =>
      obtain ⟨y, hyi, hyj, hyI⟩ := intervalTripleIntersection_nonempty
        (U i.val) (U j.val) I ⟨f x.val, x.property.1, x.property.2⟩ i.property j.property
      let s : ActiveCoverSimplex U I :=
        ⟨⟨{i.val, j.val}, Finset.insert_nonempty _ _, y,
          fun k hk => by
            rcases Finset.mem_insert.mp hk with rfl | hk
            · exact hyi
            · exact (Finset.mem_singleton.mp hk) ▸ hyj⟩,
          y, (mem_coverIntersection U _ y).mpr (fun k hk => by
            rcases Finset.mem_insert.mp hk with rfl | hk
            · exact hyi
            · exact (Finset.mem_singleton.mp hk) ▸ hyj), hyI⟩
      let z : (componentFunctor f).obj (coverIntersection U s.val) :=
        ZerothHomotopy.mk ⟨x.val, (mem_coverIntersection U s.val _).mpr (fun k hk => by
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact x.property.1
          · exact (Finset.mem_singleton.mp hk) ▸ x.property.2)⟩
      exact (categoricalMapperMemberMap_face f U I c s i (Finset.mem_insert_self _ _) z).trans
        (categoricalMapperMemberMap_face f U I c s j (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _)) z).symm
  let glue (c : Cocone (categoricalMapperDiagram f U I)) :=
    componentFunctor_existsUnique_glue f
      (fun i : ActiveCoverMember U I => toOpens (U i.val))
      (coverMember_le_saturation U I) hcov (categoricalMapperMemberMap f U I c)
      (compatible c)
  refine { desc := fun c => TypeCat.ofHom (glue c).choose, fac := ?_, uniq := ?_ }
  · intro c s
    ext e
    obtain ⟨i, hi⟩ := s.val.property.1
    have hiA : ((U i : Set ℝ) ∩ I).Nonempty := by
      obtain ⟨y, hyU, hyI⟩ := s.property
      exact ⟨y, (mem_coverIntersection U s.val y).mp hyU i hi, hyI⟩
    let j : ActiveCoverMember U I := ⟨i, hiA⟩
    let e' : (componentFunctor f).obj (toOpens (U i)) := (componentFunctor f).map (homOfLE (fun x hx =>
      (mem_coverIntersection U s.val x).mp hx i hi)) e
    have hf := (glue c).choose_spec.1 j e'
    have hmap : (componentFunctor f).map (homOfLE (coverMember_le_saturation U I j)) e' =
        (categoricalMapperCocone f U I).ι.app s e := by
      induction e using ZerothHomotopy.rec with
      | mk x => rfl
    rw [hmap] at hf
    exact hf.trans (categoricalMapperMemberMap_face f U I c s j hi e)
  · intro c m hm
    have heq : (fun x => m x) = (glue c).choose := by
      apply (glue c).choose_spec.2
      intro i e
      have hf := ConcreteCategory.congr_hom (hm (activeCoverSingleton U I i))
        ((componentFunctor f).map
          (homOfLE (coverIntersection_activeCoverSingleton U I i).ge) e)
      induction e using ZerothHomotopy.rec with
      | mk x => exact hf
    ext e
    exact congrFun heq e

end

end TDA.Mapper
