import TDA.Mapper.Tower

/-!
# Contiguity and coherent-tower fixtures

These fixtures exhibit two distinct refinement selectors with contiguous nerve
maps, a genuinely noncontiguous pair of simplicial maps, contiguity from an
empty source without inhabitedness assumptions, and a three-stage Mapper tower
whose first transition collapses an edge and whose direct map is the composite.
-/

namespace TDA.Mapper.TowerExamples

open Finset Set
open TDA.Topology
open TDA.Simplicial

noncomputable section

local instance (priority := 10000) (α : Type*) : DecidableEq α := Classical.decEq α

/-! ## Distinct refinement selectors are contiguous -/

/-- A one-member source family. -/
def selectorSource : Unit → Set Unit := fun _ => Set.univ

/-- Two distinct overlapping target members. -/
def selectorTarget : Bool → Set Unit := fun _ => Set.univ

/-- Select the first target member. -/
def selectFalse : Refinement selectorSource selectorTarget where
  selector _ := false
  subset _ := by simp [selectorSource, selectorTarget]

/-- Select the second target member. -/
def selectTrue : Refinement selectorSource selectorTarget where
  selector _ := true
  subset _ := by simp [selectorSource, selectorTarget]

/-- The two selectors give distinct vertex maps, while the common source point
witnesses contiguity of their images. -/
theorem distinct_selector_maps_are_contiguous :
    nerveMap selectFalse ≠ nerveMap selectTrue ∧
      Contiguous (nerveMap selectFalse) (nerveMap selectTrue) := by
  constructor
  · intro h
    have happ := congrArg
      (fun m : VertexMap (nerve selectorSource) (nerve selectorTarget) => m ()) h
    exact Bool.false_ne_true happ
  · exact nerveMap_contiguous selectFalse selectTrue

/-! ## Contiguity is not vacuous -/

/-- The one-member source family for the noncontiguity fixture. -/
def oneSource : Unit → Set Unit := fun _ => Set.univ

/-- Two isolated target vertices, represented by disjoint singleton members. -/
def isolatedTarget : Bool → Set Bool := fun b => {b}

/-- Send the unique ambient source vertex to one isolated target vertex. -/
def mapToIsolated (b : Bool) : VertexMap (nerve oneSource) (nerve isolatedTarget) where
  toFun _ := b
  map_face := by
    intro s hs
    obtain ⟨hsn, _, _⟩ := (mem_nerve_iff oneSource s).1 hs
    refine (mem_nerve_iff isolatedTarget _).2
      ⟨Finset.image_nonempty.mpr hsn, b, ?_⟩
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    simp [isolatedTarget]

/-- Maps from a singleton source to two distinct isolated vertices are not
contiguous. -/
theorem isolated_vertex_maps_are_not_contiguous :
    ¬ Contiguous (mapToIsolated false) (mapToIsolated true) := by
  intro h
  have hsource : ({()} : Finset Unit) ∈ nerve oneSource := by
    simp [mem_nerve_iff, oneSource]
  have htarget := h {()} hsource
  have hpair : ({false, true} : Finset Bool) ∈ nerve isolatedTarget := by
    simpa [mapToIsolated] using htarget
  obtain ⟨_, x, hx⟩ := (mem_nerve_iff isolatedTarget _).1 hpair
  have hfalse := hx false (by simp)
  have htrue := hx true (by simp)
  simp [isolatedTarget] at hfalse htrue
  exact Bool.false_ne_true (hfalse.symm.trans htrue)

/-- An empty source complex makes every pair of maps contiguous, with no
inhabitedness assumption on either ambient vertex type.  The target may have
arbitrary unsupported ghost vertices. -/
theorem empty_source_maps_are_contiguous {I : Type*} {J : Type*}
    (L : PreAbstractSimplicialComplex J)
    (a b : VertexMap (⊥ : PreAbstractSimplicialComplex I) L) :
    Contiguous a b := by
  intro s hs
  exact hs.elim

/-! ## A dependent-index three-stage tower -/

/-- Three ordered stages for the coherent-tower fixture. -/
inductive ThreeStage
  | first
  | middle
  | last
  deriving DecidableEq

/-- The six comparisons in the three-stage preorder. -/
inductive ThreeStageLE : ThreeStage → ThreeStage → Prop
  | first_refl : ThreeStageLE .first .first
  | middle_refl : ThreeStageLE .middle .middle
  | last_refl : ThreeStageLE .last .last
  | first_middle : ThreeStageLE .first .middle
  | middle_last : ThreeStageLE .middle .last
  | first_last : ThreeStageLE .first .last

instance : LE ThreeStage := ⟨ThreeStageLE⟩

instance : Preorder ThreeStage where
  le_refl p := by cases p <;> constructor
  le_trans _ _ _ h k := by cases h <;> cases k <;> constructor

/-- The dependent index types vary across the three stages. -/
def threeStageIndex : ThreeStage → Type
  | .first => Bool
  | .middle => Unit
  | .last => Fin 2

/-- Every member of the example cover family is the full one-point space. -/
def threeStageCover (p : ThreeStage) : threeStageIndex p → Set Unit :=
  fun _ => Set.univ

/-- The coherent selector collapses both first-stage indices at the middle
stage and chooses vertex `0` at the last stage. -/
def threeStageSelector (p q : ThreeStage) (h : p ≤ q) :
    threeStageIndex p → threeStageIndex q :=
  match p, q with
  | .first, .first => id
  | .first, .middle => fun _ => ()
  | .first, .last => fun _ => (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)
  | .middle, .first => False.elim (by cases h)
  | .middle, .middle => id
  | .middle, .last => fun _ => (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)
  | .last, .first => False.elim (by cases h)
  | .last, .middle => False.elim (by cases h)
  | .last, .last => id

/-- The selected refinement at each comparison of the example tower. -/
def threeStageRefinement {p q : ThreeStage} (h : p ≤ q) :
    Refinement (threeStageCover p) (threeStageCover q) where
  selector := threeStageSelector p q h
  subset _ := by simp [threeStageCover]

private theorem threeStageSelector_refl (p : ThreeStage) :
    threeStageSelector p p (le_refl p) = id := by
  cases p <;> rfl

private theorem threeStageSelector_trans {p q r : ThreeStage}
    (h : p ≤ q) (k : q ≤ r) :
    threeStageSelector q r k ∘ threeStageSelector p q h =
      threeStageSelector p r (h.trans k) := by
  cases p <;> cases q <;> cases r <;>
    cases h <;> cases k <;> funext i <;> rfl

/-- The coherent three-stage cover tower with genuinely varying index types. -/
def threeStageTower : CoherentCoverTower Unit ThreeStage where
  Index := threeStageIndex
  cover := threeStageCover
  refinement := threeStageRefinement
  selector_refl := threeStageSelector_refl
  selector_trans := threeStageSelector_trans

/-- The constant map used by the three-stage Mapper tower. -/
def threeStageMap : C(Unit, Unit) := ContinuousMap.const Unit ()

/-- The component-cover index represented by the unique domain point. -/
def threeStageComponentIndex (p : ThreeStage) (i : threeStageIndex p) :
    ComponentIndex threeStageMap (threeStageCover p) :=
  ⟨i, ZerothHomotopy.mk ⟨(), Set.mem_univ ()⟩⟩

private theorem first_le_middle : ThreeStage.first ≤ ThreeStage.middle :=
  ThreeStageLE.first_middle
private theorem middle_le_last : ThreeStage.middle ≤ ThreeStage.last :=
  ThreeStageLE.middle_last
private theorem first_le_last : ThreeStage.first ≤ ThreeStage.last :=
  ThreeStageLE.first_last

private theorem threeStageMapperMap_apply {p q : ThreeStage} (h : p ≤ q)
    (i : threeStageIndex p) :
    TDA.Mapper.mapperMap threeStageMap (threeStageRefinement h)
        (threeStageComponentIndex p i) =
      threeStageComponentIndex q (threeStageSelector p q h i) := by
  rfl

private theorem firstMiddleMapperMap_apply (b : Bool) :
    TDA.Mapper.mapperMap threeStageMap (threeStageRefinement first_le_middle)
        (threeStageComponentIndex .first b) =
      threeStageComponentIndex .middle () := by
  rfl

/-- The direct first-to-last Mapper map is the composite of the two adjacent
maps, and the first transition collapses the displayed source edge to the
middle-stage vertex. -/
theorem three_stage_tower_composite_and_collapsing_edge :
    threeStageTower.mapperMap threeStageMap first_le_last =
        VertexMap.comp
          (threeStageTower.mapperMap threeStageMap first_le_middle)
          (threeStageTower.mapperMap threeStageMap middle_le_last) ∧
      threeStageComponentIndex .first false ≠
        threeStageComponentIndex .first true ∧
      ({threeStageComponentIndex .first false,
          threeStageComponentIndex .first true} :
          Finset (ComponentIndex threeStageMap (threeStageCover .first))) ∈
        threeStageTower.mapperComplex threeStageMap .first ∧
      (({threeStageComponentIndex .first false,
          threeStageComponentIndex .first true} :
          Finset (ComponentIndex threeStageMap (threeStageCover .first))).image
          (TDA.Mapper.mapperMap threeStageMap
            (threeStageRefinement first_le_middle))) =
        {threeStageComponentIndex .middle ()} := by
  refine ⟨(threeStageTower.mapperMap_trans threeStageMap
      first_le_middle middle_le_last).symm, ?_, ?_, ?_⟩
  · intro h
    exact Bool.false_ne_true (congrArg Sigma.fst h)
  · apply (mem_mapper_iff threeStageMap (threeStageCover .first) _).2
    refine ⟨by simp, (), ?_⟩
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> exact ⟨Set.mem_univ (), rfl⟩
  · ext a
    constructor
    · intro ha
      obtain ⟨i, hi, hmap⟩ := Finset.mem_image.mp ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · rw [firstMiddleMapperMap_apply] at hmap
        exact Finset.mem_singleton.mpr hmap.symm
      · rw [firstMiddleMapperMap_apply] at hmap
        exact Finset.mem_singleton.mpr hmap.symm
    · intro ha
      have ha' := Finset.mem_singleton.mp ha
      subst a
      exact Finset.mem_image.mpr
        ⟨threeStageComponentIndex .first false, by simp, by
          exact firstMiddleMapperMap_apply false⟩

end

end TDA.Mapper.TowerExamples
