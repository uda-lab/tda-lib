import TDA.Persistence.F2GridHomologyInput
import TDA.Persistence.FiniteSimplicialPresentation
import TDA.Persistence.RankErosion
import TDA.Simplicial.ContiguityHomotopy

/-!
# The generated F₂ grid representation computes the homology

For valid rationally graded input `xs` and a degree `p`, the Kan extension of the grid module of
`RatGradedInput.toF2GridRep xs p` is isomorphic, as a persistence module over F₂ on real
grades, to the actual homology `RatGradedInput.homology xs h p`
(`RatGradedInput.toF2GridRep_lanIso`). The isomorphism is canonical
(`RatGradedInput.kanInclusion_toF2GridRep_lanIso`): below a grade with a lower grid point it is
the generated fibre at the grid floor, read in the computed coordinates of its slice, followed
by the actual inclusion from the floor.

The proof has three steps.

* The relabelling `Fin.val` from an actual sublevel to the single sublevel of its slice induces
  an isomorphism on homology (`RatGradedInput.isIso_sliceVertexMap`). For `m ≥ 1`, a retraction
  `ℕ → Fin m` is a vertex map back, and the composite on the slice is contiguous to the identity;
  with no vertices both complexes are empty.
* In the resulting coordinates (`RatGradedInput.sliceCoordinates`) the generated matrix between
  two comparable rational grades is the matrix of the actual inclusion-induced map
  (`RatGradedInput.sliceCoordinates_structureMap`), so the grid module of the generated
  representation is the grid restriction of the actual homology
  (`RatGradedInput.gridModuleIso`).
* The canonical Kan comparison `CoordinateGrid.kanComparisonIso` extends this from the grid to
  all real grades, using that every sublevel equals the sublevel at its grid floor and is empty
  without a lower grid point.

Consequences: generated fibre dimensions are actual Betti numbers at every rational grade
(`RatGradedInput.toF2GridRep_dim`), executable ranks are the ranks of the actual structure maps
(`RatGradedInput.toF2GridRep_rankAt`), and weak-pair rank erosion and its distance between the
Kan extensions of two generated representations are those of the actual homology modules.

The end-to-end erosion test of two inputs is separate.
-/

set_option autoImplicit false

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits
open TDA.Simplicial TDA.Filtration
open TDA.Persistence.Reduction

namespace RatGradedInput

variable {m n : ℕ}

/-- The relabelling `Fin.val` maps each actual sublevel at a rational grade onto the single
sublevel of its slice. -/
def sliceVertexMap {xs : RatGradedInput m n} (h : Valid xs) (u : Fin n → ℚ) :
    VertexMap ((toGraded xs h).sublevel (RatGrid.realGrade u))
      ((FiniteInput.gradeFilter (slice xs u) (slice_valid h u)).sublevel 0) where
  toFun := Fin.val
  map_face s hs := by
    have he : @Finset.image (Fin m) ℕ (Classical.decEq ℕ) Fin.val s =
        s.map Fin.valEmbedding := by
      ext x
      simp
    rw [he]
    exact (mem_sublevel_slice_iff h u _).mpr ⟨s, hs, rfl⟩

private def retract (k : ℕ) (i : ℕ) : Fin (k + 1) := if hi : i < k + 1 then ⟨i, hi⟩ else 0

private theorem retract_val (k : ℕ) (i : Fin (k + 1)) : retract k i.val = i := by
  simp [retract, i.isLt]

private def sliceRetract {k : ℕ} {xs : RatGradedInput (k + 1) n} (h : Valid xs)
    (u : Fin n → ℚ) :
    VertexMap ((FiniteInput.gradeFilter (slice xs u) (slice_valid h u)).sublevel 0)
      ((toGraded xs h).sublevel (RatGrid.realGrade u)) where
  toFun := retract k
  map_face s hs := by
    obtain ⟨t, ht, rfl⟩ := (mem_sublevel_slice_iff h u s).mp hs
    have he : @Finset.image ℕ (Fin (k + 1)) (Classical.decEq _) (retract k)
        (t.map Fin.valEmbedding) = t := by
      ext x
      simp [retract_val]
    rw [he]
    exact ht

/-- The relabelling induces an isomorphism on homology in every degree. -/
instance isIso_sliceVertexMap {xs : RatGradedInput m n} (h : Valid xs) (u : Fin n → ℚ)
    (p : ℕ) : IsIso (simplicialHomologyMap (ZMod 2) (sliceVertexMap h u) p) := by
  cases m with
  | zero =>
    have hK : (toGraded xs h).sublevel (RatGrid.realGrade u) = ⊥ := by
      apply ((toGraded xs h).sublevel_eq_bot_iff _).mpr
      intro s
      exact absurd ((toComplex xs h).nonempty s.val s.property) (by
        rw [Finset.not_nonempty_iff_eq_empty]
        exact Subsingleton.elim _ _)
    have hL : (FiniteInput.gradeFilter (slice xs u) (slice_valid h u)).sublevel 0 = ⊥ := by
      apply eq_bot_iff.mpr
      intro s hs
      obtain ⟨t, ht, rfl⟩ := (mem_sublevel_slice_iff h u s).mp hs
      rw [hK] at ht
      exact ht
    refine IsZero.isIso ?_ ?_ _
    · rw [hK]; exact isZero_simplicialHomology_bot (ZMod 2) p
    · rw [hL]; exact isZero_simplicialHomology_bot (ZMod 2) p
  | succ k =>
    refine ⟨simplicialHomologyMap (ZMod 2) (sliceRetract h u) p, ?_, ?_⟩
    · rw [← simplicialHomologyMap_comp]
      have he : VertexMap.comp (sliceVertexMap h u) (sliceRetract h u) =
          VertexMap.id _ := VertexMap.ext fun i => retract_val k i
      rw [he, simplicialHomologyMap_id]
    · rw [← simplicialHomologyMap_comp, ← simplicialHomologyMap_id]
      apply Contiguous.simplicialHomologyMap_eq
      intro s hs
      obtain ⟨t, ht, rfl⟩ := (mem_sublevel_slice_iff h u s).mp hs
      convert hs using 1
      ext x
      simp [VertexMap.comp, VertexMap.id, sliceRetract, sliceVertexMap, retract_val]

/-- Coordinates of the actual homology at a rational grade in the computed basis of its slice:
relabelling followed by the existing computed coordinates. -/
noncomputable def sliceCoordinates {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ)
    (u : Fin n → ℚ) :
    (homology xs h p).obj (RatGrid.realGrade u) ≃ₗ[ZMod 2]
      (Fin ((toF2GridRep xs p).dim u) → ZMod 2) :=
  (asIso (simplicialHomologyMap (ZMod 2) (sliceVertexMap h u) p)).toLinearEquiv.trans
    (FiniteInput.sublevelCoordinates (slice xs u) (slice_valid h u) p 0)

/-- The generated matrix between two comparable rational grades is the matrix of the actual
inclusion-induced homology map in the slice coordinates. -/
theorem sliceCoordinates_structureMap {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ)
    {u v : Fin n → ℚ} (huv : u ≤ v) (x : (homology xs h p).obj (RatGrid.realGrade u)) :
    sliceCoordinates h p v
        (structureMapLinear (homology xs h p) (RatGrid.realGrade_le_iff.mpr huv) x) =
      ((toF2GridRep xs p).map u v).mulVec (sliceCoordinates h p u x) := by
  have hnat : VertexMap.comp (inclusionVertexMap
        ((toGraded xs h).sublevel_mono (RatGrid.realGrade_le_iff.mpr huv)))
        (sliceVertexMap h v) =
      VertexMap.comp (sliceVertexMap h u)
        (FiniteInput.validatedVertexMap (slice xs u) (slice xs v) (slice_valid h u)
          (slice_valid h v) 0 0 id (vertexMapCondition_slice huv)) :=
    VertexMap.ext fun _ => rfl
  have hx := congrArg (fun f => f.hom x)
    (congrArg (fun f => simplicialHomologyMap (ZMod 2) f p) hnat)
  simp only [simplicialHomologyMap_comp, simplicialHomologyMap_inclusion] at hx
  have hx' : (simplicialHomologyMap (ZMod 2) (sliceVertexMap h v) p).hom
        (structureMapLinear (homology xs h p) (RatGrid.realGrade_le_iff.mpr huv) x) =
      (simplicialHomologyMap (ZMod 2)
        (FiniteInput.validatedVertexMap (slice xs u) (slice xs v) (slice_valid h u)
          (slice_valid h v) 0 0 id (vertexMapCondition_slice huv)) p).hom
        ((simplicialHomologyMap (ZMod 2) (sliceVertexMap h u) p).hom x) := hx
  change FiniteInput.sublevelCoordinates (slice xs v) (slice_valid h v) p 0
      ((simplicialHomologyMap (ZMod 2) (sliceVertexMap h v) p).hom
        (structureMapLinear (homology xs h p) (RatGrid.realGrade_le_iff.mpr huv) x)) = _
  rw [hx', FiniteInput.homologyMapMatrix_correct]
  rfl

/-- On a grid grade, the generated fibre is the actual homology at its real grade. -/
noncomputable def gridPointEquiv {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ)
    (q : (toF2GridRep xs p).grid.Point) :
    ((toF2GridRep xs p).toModule (toF2GridRep_valid h p)).obj q ≃ₗ[ZMod 2]
      (homology xs h p).obj ((gridValues xs).grid.embedding q) :=
  (sliceCoordinates h p ((gridValues xs).ratPoint q)).symm.trans
    ((homology xs h p).mapIso
      (eqToIso (RatGrid.realGrade_ratPoint (gridValues xs) q))).toLinearEquiv

-- The rewrites at the grid fibres need the relaxed transparency check. Without it,
-- `rw [LinearEquiv.apply_symm_apply]` finds no occurrence: the coercions of the generated fibre,
-- a `ModuleCat` carrier, agree with those in `sliceCoordinates_structureMap` only after unfolding
-- beyond the transparency that the default check allows.
set_option backward.isDefEq.respectTransparency false in
/-- The grid module of the generated representation is the grid restriction of the actual
homology, as persistence modules. -/
noncomputable def gridModuleIso {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ) :
    (toF2GridRep xs p).toModule (toF2GridRep_valid h p) ≅
      (gridValues xs).grid.embedding.monotone.functor ⋙ homology xs h p :=
  NatIso.ofComponents (fun q => (gridPointEquiv h p q).toModuleIso) (by
    intro q q' f
    have hqq' : (gridValues xs).ratPoint q ≤ (gridValues xs).ratPoint q' :=
      (gridValues xs).ratPoint_le_iff.mpr (leOfHom f)
    ext x
    have hc := sliceCoordinates_structureMap h p hqq'
      ((sliceCoordinates h p ((gridValues xs).ratPoint q)).symm x)
    rw [LinearEquiv.apply_symm_apply] at hc
    have hy := ((sliceCoordinates h p ((gridValues xs).ratPoint q')).symm_apply_eq).mpr hc.symm
    change (homology xs h p).map (eqToHom (RatGrid.realGrade_ratPoint (gridValues xs) q'))
        ((sliceCoordinates h p ((gridValues xs).ratPoint q')).symm
          (((toF2GridRep xs p).map ((gridValues xs).ratPoint q)
            ((gridValues xs).ratPoint q')).mulVec x)) =
      (homology xs h p).map (homOfLE ((gridValues xs).grid.embedding.monotone (leOfHom f)))
        ((homology xs h p).map (eqToHom (RatGrid.realGrade_ratPoint (gridValues xs) q))
          ((sliceCoordinates h p ((gridValues xs).ratPoint q)).symm x))
    rw [hy]
    change ((homology xs h p).map _ ≫ (homology xs h p).map _) _ =
      ((homology xs h p).map _ ≫ (homology xs h p).map _) _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl)

/-- **The generated representation computes the actual homology.** For valid input and every
degree, the Kan extension of the grid module of the generated representation is isomorphic, as
a persistence module over F₂ on real grades, to the actual inclusion-induced homology. -/
noncomputable def toF2GridRep_lanIso {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ) :
    (toF2GridRep xs p).grid.lan.obj ((toF2GridRep xs p).toModule (toF2GridRep_valid h p)) ≅
      homology xs h p :=
  (gridValues xs).grid.lan.mapIso (gridModuleIso h p) ≪≫
    (gridValues xs).grid.kanComparisonIso (homology xs h p)
      (fun a ha => by
        rw [finiteSimplicialHomology_structureMap]
        exact simplicialHomologyIncl_isIso_of_eq (ZMod 2) _ (sublevel_floor h a ha) p)
      (fun a ha => by
        rw [finiteSimplicialHomology_obj, sublevel_eq_bot_of_not_hasLowerPoint h a ha]
        exact isZero_simplicialHomology_bot (ZMod 2) p)

-- The rewrite with `kanInclusion_naturality` needs the relaxed transparency check. Without it,
-- the preceding `rw [← Category.assoc]` finds no occurrence: the composites of the left Kan
-- extension and of the persistence-module category agree only after unfolding beyond the
-- transparency that the default check allows.
set_option backward.isDefEq.respectTransparency false in
/-- Below a real grade with a lower grid point, the isomorphism reads the generated fibre at the
grid floor in its slice coordinates and maps it into the actual homology by the inclusion from
the floor. -/
theorem kanInclusion_toF2GridRep_lanIso {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ)
    (a : Fin n → ℝ) (ha : (gridValues xs).grid.HasLowerPoint a) :
    (gridValues xs).grid.kanInclusion _ a ha ≫ (toF2GridRep_lanIso h p).hom.app a =
      (gridPointEquiv h p ((gridValues xs).grid.floor a ha)).toModuleIso.hom ≫
        structureMap (homology xs h p) ((gridValues xs).grid.floor_le a ha) := by
  change (gridValues xs).grid.kanInclusion _ a ha ≫
      ((gridValues xs).grid.lan.map (gridModuleIso h p).hom).app a ≫
        ((gridValues xs).grid.kanComparison (homology xs h p)).app a = _
  rw [← Category.assoc, CoordinateGrid.kanInclusion_naturality, Category.assoc,
    CoordinateGrid.kanInclusion_kanComparison]
  rfl

/-- The fibre dimension of the generated representation at any rational grade is the actual
Betti number there. -/
theorem toF2GridRep_dim {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ) (u : Fin n → ℚ) :
    (toF2GridRep xs p).dim u =
      Module.finrank (ZMod 2) ((homology xs h p).obj (RatGrid.realGrade u)) := by
  rw [(sliceCoordinates h p u).finrank_eq, Module.finrank_fin_fun]

/-- The executable rank of the generated representation is the rank of the actual homology
structure map between the real grades. -/
theorem toF2GridRep_rankAt {xs : RatGradedInput m n} (h : Valid xs) (p : ℕ)
    {x y : Fin n → ℚ} (hxy : x ≤ y) :
    (toF2GridRep xs p).rankAt x y =
      rankOfStructureMap (homology xs h p) (RatGrid.realGrade_le_iff.mpr hxy) := by
  rw [(toF2GridRep xs p).rankAt_eq (toF2GridRep_valid h p) hxy]
  exact rankOfStructureMap_iso _ (toF2GridRep_lanIso h p)

variable {m' : ℕ}

/-- Erosion between the Kan extensions of two generated representations is erosion between the
actual homology modules. -/
theorem rankErosion_lan_toF2GridRep_iff {xs : RatGradedInput m n} {ys : RatGradedInput m' n}
    (hx : Valid xs) (hy : Valid ys) (p : ℕ) (ε : NNReal) :
    RankErosion ε ((toF2GridRep xs p).grid.lan.obj ((toF2GridRep xs p).toModule
        (toF2GridRep_valid hx p)))
      ((toF2GridRep ys p).grid.lan.obj ((toF2GridRep ys p).toModule (toF2GridRep_valid hy p))) ↔
      RankErosion ε (homology xs hx p) (homology ys hy p) :=
  rankErosion_iff_of_iso (toF2GridRep_lanIso hx p) (toF2GridRep_lanIso hy p)

/-- The erosion distance of the Kan extensions of two generated representations is that of the
actual homology modules. -/
theorem rankErosionDistance_lan_toF2GridRep {xs : RatGradedInput m n}
    {ys : RatGradedInput m' n} (hx : Valid xs) (hy : Valid ys) (p : ℕ) :
    rankErosionDistance ((toF2GridRep xs p).grid.lan.obj ((toF2GridRep xs p).toModule
        (toF2GridRep_valid hx p)))
      ((toF2GridRep ys p).grid.lan.obj ((toF2GridRep ys p).toModule (toF2GridRep_valid hy p))) =
      rankErosionDistance (homology xs hx p) (homology ys hy p) :=
  rankErosionDistance_eq_of_iso (toF2GridRep_lanIso hx p) (toF2GridRep_lanIso hy p)

end RatGradedInput

end TDA.Persistence
