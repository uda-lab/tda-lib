import TDA.Persistence.SubdivisionRips
import TDA.Topology.MulticoverCover
import TDA.Simplicial.ContiguityHomotopy
import TDA.Simplicial.BarycentricHomology

/-!
# The concrete multicover nerve comparison on homology

The normalized Čech flag complex includes into the nerve of its large-face
cover. This inclusion induces a natural morphism of actual simplicial homology
bifiltrations. Finite sup-norm coordinates identify its source with normalized
subdivision-Rips homology, and the inclusion is a natural isomorphism on
homology by the union/all-large-subfaces comparison.
-/

universe u v
noncomputable section
namespace TDA.Persistence.SubdivisionRips
open CategoryTheory TDA.Simplicial TDA.Filtration.SubdivisionRips
open TDA.Topology.MeasureBifiltration
attribute [local instance] vertexOrder
variable {V : Type v} [Fintype V]
variable (R : Type u) [Ring R]
local instance : DecidableEq V := Classical.decEq V

/-- The concrete flag-to-cover-nerve inclusion induces a natural morphism of
actual simplicial homology bifiltrations. -/
noncomputable def cechHomologyToLargeFaceNerve {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (n : ℕ) :
    simplicialHomologyPModule R (cechBifiltration p) n ⟶
      simplicialHomologyPModule R (largeFaceNerveBifiltration p) n where
  app a := simplicialHomologyIncl R (subdivision_openCech_le_largeFaceNerve p a) n
  naturality := by
    intro a b f
    change simplicialHomologyIncl R _ n ≫ simplicialHomologyIncl R _ n =
      simplicialHomologyIncl R _ n ≫ simplicialHomologyIncl R _ n
    let h₁ := (cechBifiltration p).monotone (leOfHom f)
    let h₂ := subdivision_openCech_le_largeFaceNerve p b
    let h₃ := subdivision_openCech_le_largeFaceNerve p a
    let h₄ := (largeFaceNerveBifiltration p).monotone (leOfHom f)
    exact (simplicialHomologyIncl_comp R h₁ h₂ n).symm.trans
      (simplicialHomologyIncl_comp R h₃ h₄ n)

/-- For isometric finite sup-norm coordinates, the source of the natural
cover-nerve comparison is exactly the concrete normalized subdivision-Rips module. -/
noncomputable def ripsHomologyToLargeFaceNerve {ι : Type*} [Fintype ι]
    (d : MetricSpace V) (p : V → ι → ℝ)
    (hd : ∀ v w, d.dist v w = dist (p v) (p w)) (n : ℕ) :
    homology R d n ⟶ simplicialHomologyPModule R (largeFaceNerveBifiltration p) n := by
  rw [← cechHomology_eq R d p hd n]
  exact cechHomologyToLargeFaceNerve R p n

private def largeFaceSubfaces {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (U : Finset V) : Finset (Finset V) := by
  classical
  exact insert U (Finset.univ.filter fun s =>
    s ⊆ U ∧ s ∈ openCech p (radius a) ∧
      mass a ≤ (s.card : ℝ) / Fintype.card V)

private theorem mem_largeFaceSubfaces {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (U s : Finset V) :
    s ∈ largeFaceSubfaces p a U ↔
      s = U ∨ (s ⊆ U ∧ s ∈ openCech p (radius a) ∧
        mass a ≤ (s.card : ℝ) / Fintype.card V) := by
  classical
  simp [largeFaceSubfaces]

private theorem largeFaceSubfaces_biUnion {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (U : Finset V) :
    (largeFaceSubfaces p a U).biUnion id = U := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hv
    rcases (mem_largeFaceSubfaces p a U s).mp hs with hEq | hsmall
    · simpa [hEq] using hvs
    · exact hsmall.1 hvs
  · intro v hv
    exact Finset.mem_biUnion.mpr ⟨U, Finset.mem_insert_self _ _, hv⟩

private theorem largeFaceSubfaces_mono {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) {U W : Finset V}
    (hU : U ∈ openCech p (radius a))
    (hlarge : mass a ≤ (U.card : ℝ) / Fintype.card V)
    (hUW : U ⊆ W) : largeFaceSubfaces p a U ⊆ largeFaceSubfaces p a W := by
  intro s hs
  rcases (mem_largeFaceSubfaces p a U s).mp hs with hEq | hsmall
  · subst s
    apply (mem_largeFaceSubfaces p a W U).2
    right
    exact ⟨hUW, hU, hlarge⟩
  · apply (mem_largeFaceSubfaces p a W s).2
    right
    exact ⟨hsmall.1.trans hUW, hsmall.2.1, hsmall.2.2⟩

private theorem largeFaceNerve_face_of_subfaces {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (S : Finset (Finset V)) (U : Finset V)
    (hS : S.Nonempty)
    (hvalid : ∀ s ∈ S, s ∈ openCech p (radius a) ∧
      mass a ≤ (s.card : ℝ) / Fintype.card V)
    (hbelow : S.biUnion id ⊆ U)
    (hU : U ∈ openCech p (radius a)) :
    S ∈ largeFaceNerveBifiltration p a := by
  apply (mem_largeFaceNerve_iff p a S).2
  refine ⟨hS, hvalid, ?_⟩
  have hUnionNonempty : (S.biUnion id).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    obtain ⟨v, hv⟩ := (hvalid s hs).1.1
    exact ⟨v, Finset.mem_biUnion.mpr ⟨s, hs, hv⟩⟩
  exact (openCech p (radius a)).isRelLowerSet_faces hU |>.2 hbelow hUnionNonempty

private theorem largeFaceNerve_union_mem {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) {S : Finset (Finset V)}
    (hS : S ∈ largeFaceNerveBifiltration p a) :
    S.biUnion id ∈ openCech p (radius a) ∧
      mass a ≤ ((S.biUnion id).card : ℝ) / Fintype.card V := by
  have hdata := (mem_largeFaceNerve_iff p a S).mp hS
  refine ⟨hdata.2.2, ?_⟩
  obtain ⟨s, hs⟩ := hdata.1
  have hsub : s ⊆ S.biUnion id := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨s, hs, hv⟩
  have hcard := Finset.card_le_card hsub
  have hcardReal : (s.card : ℝ) ≤ ((S.biUnion id).card : ℝ) := by
    exact_mod_cast hcard
  exact (hdata.2.1 s hs).2.trans
    (div_le_div_of_nonneg_right hcardReal (by positivity))

private theorem largeFaceSubfaces_mem_nerve {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (U : Finset V)
    (hU : U ∈ openCech p (radius a))
    (hlarge : mass a ≤ (U.card : ℝ) / Fintype.card V) :
    largeFaceSubfaces p a U ∈ largeFaceNerveBifiltration p a := by
  apply largeFaceNerve_face_of_subfaces p a _ U
  · exact ⟨U, Finset.mem_insert_self _ _⟩
  · intro s hs
    rcases (mem_largeFaceSubfaces p a U s).mp hs with hEq | hsmall
    · subst s
      exact ⟨hU, hlarge⟩
    · exact ⟨hsmall.2.1, hsmall.2.2⟩
  · rw [largeFaceSubfaces_biUnion]
  · exact hU

private def largeFaceUnionVertexMap {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) :
    VertexMap (barycentricSubdivision (TDA.Topology.nerve (largeFaceCover p a)))
      (subdivision (openCech p (radius a)) (mass a)) where
  toFun S := S.biUnion id
  map_face := by
    classical
    letI : DecidableEq (Finset V) := Classical.decEq _
    intro C hC
    change C ∈ barycentricSubdivision (TDA.Topology.nerve (largeFaceCover p a)) at hC
    have hflag := (mem_subdivision_iff
      (TDA.Topology.nerve (largeFaceCover p a)) 0 C).mp hC
    change C.image (fun S => S.biUnion id) ∈
      subdivision (openCech p (radius a)) (mass a)
    apply (mem_subdivision_iff (openCech p (radius a)) (mass a) _).2
    refine ⟨Finset.image_nonempty.mpr hflag.1, ?_, ?_⟩
    · intro U hU
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
      exact largeFaceNerve_union_mem p a (hflag.2.1 S hS).1
    · intro U hU W hW
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hW
      rcases hflag.2.2 S hS T hT with hST | hTS
      · apply Or.inl
        intro v hv
        obtain ⟨S, hS, hv⟩ := Finset.mem_biUnion.mp hv
        exact Finset.mem_biUnion.mpr ⟨S, hST hS, hv⟩
      · apply Or.inr
        intro v hv
        obtain ⟨T, hT, hv⟩ := Finset.mem_biUnion.mp hv
        exact Finset.mem_biUnion.mpr ⟨T, hTS hT, hv⟩

private def largeFaceSubfacesVertexMap {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) :
    VertexMap (subdivision (openCech p (radius a)) (mass a))
      (barycentricSubdivision (TDA.Topology.nerve (largeFaceCover p a))) where
  toFun U := largeFaceSubfaces p a U
  map_face := by
    classical
    letI : DecidableEq (Finset (Finset V)) := Classical.decEq _
    intro C hC
    change C ∈ subdivision (openCech p (radius a)) (mass a) at hC
    have hflag := (mem_subdivision_iff
      (openCech p (radius a)) (mass a) C).mp hC
    change C.image (largeFaceSubfaces p a) ∈
      barycentricSubdivision (TDA.Topology.nerve (largeFaceCover p a))
    apply (mem_subdivision_iff (TDA.Topology.nerve (largeFaceCover p a)) 0 _).2
    refine ⟨Finset.image_nonempty.mpr hflag.1, ?_, ?_⟩
    · intro S hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hS
      have hlarge := (hflag.2.1 U hU).2
      have hcech := (hflag.2.1 U hU).1
      refine ⟨largeFaceSubfaces_mem_nerve p a U hcech hlarge, ?_⟩
      positivity
    · intro S hS T hT
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hT
      rcases hflag.2.2 U hU W hW with hUW | hWU
      · exact Or.inl (largeFaceSubfaces_mono p a
          (hflag.2.1 U hU).1 (hflag.2.1 U hU).2 hUW)
      · exact Or.inr (largeFaceSubfaces_mono p a
          (hflag.2.1 W hW).1 (hflag.2.1 W hW).2 hWU)

private theorem largeFaceSubfaces_union_map_eq_id {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) :
    VertexMap.comp (largeFaceSubfacesVertexMap p a)
        (largeFaceUnionVertexMap p a) =
    VertexMap.id (subdivision (openCech p (radius a)) (mass a)) := by
  apply VertexMap.ext
  intro U
  change (largeFaceSubfaces p a U).biUnion id = U
  exact largeFaceSubfaces_biUnion p a U

private theorem flag_maximum_subset {W : Type*}
    (S : Finset (Finset W)) (hne : S.Nonempty)
    (hchain : ∀ s ∈ S, ∀ t ∈ S, s ⊆ t ∨ t ⊆ s) :
    ∃ t ∈ S, ∀ s ∈ S, s ⊆ t := by
  classical
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image S Finset.card hne
  refine ⟨t, ht, ?_⟩
  intro s hs
  rcases hchain s hs t ht with hst | hts
  · exact hst
  · have heq : t = s := Finset.eq_of_subset_of_card_le hts (hmax s hs)
    simpa [heq]

private theorem faceUnion_inclusion_contiguous_lastVertex {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) :
    Contiguous
      (VertexMap.comp (largeFaceUnionVertexMap p a)
        (inclusionVertexMap (subdivision_openCech_le_largeFaceNerve p a)))
      (lastVertexMap (TDA.Topology.nerve (largeFaceCover p a))) := by
  classical
  letI : DecidableEq (Finset V) := Classical.decEq _
  intro C hC
  change C ∈ barycentricSubdivision (TDA.Topology.nerve (largeFaceCover p a)) at hC
  have hflag := (mem_subdivision_iff
    (TDA.Topology.nerve (largeFaceCover p a)) 0 C).mp hC
  obtain ⟨T, hT, hmax⟩ := flag_maximum_subset C hflag.1 hflag.2.2
  have hTvalid := largeFaceNerve_union_mem p a (hflag.2.1 T hT).1
  let labels := C.image (fun S => S.biUnion id) ∪ C.image (fun S => lastVertex S)
  have hlabels : labels ∈ largeFaceNerveBifiltration p a := by
    apply largeFaceNerve_face_of_subfaces p a labels (T.biUnion id)
    · obtain ⟨S, hS⟩ := hflag.1
      exact ⟨S.biUnion id,
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩)⟩
    · intro s hs
      rcases Finset.mem_union.mp hs with hs | hs
      · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
        exact largeFaceNerve_union_mem p a (hflag.2.1 S hS).1
      · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
        have hdata := (mem_largeFaceNerve_iff p a S).mp (hflag.2.1 S hS).1
        have hlast : lastVertex S ∈ S := by
          rw [lastVertex_of_nonempty S hdata.1]
          exact Finset.max'_mem S hdata.1
        exact hdata.2.1 _ hlast
    · intro v hv
      obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hv
      rcases Finset.mem_union.mp hs with hs | hs
      · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hvs
        exact Finset.mem_biUnion.mpr ⟨t, hmax S hS ht, hvt⟩
      · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hs
        have hdata := (mem_largeFaceNerve_iff p a S).mp (hflag.2.1 S hS).1
        have hlast : lastVertex S ∈ S := by
          rw [lastVertex_of_nonempty S hdata.1]
          exact Finset.max'_mem S hdata.1
        exact Finset.mem_biUnion.mpr ⟨lastVertex S, hmax S hS hlast, hvs⟩
    · exact hTvalid.1
  change labels ∈ largeFaceNerveBifiltration p a
  exact hlabels

private theorem inclusion_contiguous_subfaces_lastVertex {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) :
    Contiguous
      (inclusionVertexMap (subdivision_openCech_le_largeFaceNerve p a))
      (VertexMap.comp (largeFaceSubfacesVertexMap p a)
        (lastVertexMap (TDA.Topology.nerve (largeFaceCover p a)))) := by
  classical
  letI : DecidableEq (Finset V) := Classical.decEq _
  intro C hC
  change C ∈ subdivision (openCech p (radius a)) (mass a) at hC
  have hflag := (mem_subdivision_iff
    (openCech p (radius a)) (mass a) C).mp hC
  obtain ⟨U, hU, hmax⟩ := flag_maximum_subset C hflag.1 hflag.2.2
  have hUvalid := hflag.2.1 U hU
  let labels := C ∪ C.image (fun W => lastVertex (largeFaceSubfaces p a W))
  have hlabels : labels ∈ largeFaceNerveBifiltration p a := by
    apply largeFaceNerve_face_of_subfaces p a labels U
    · obtain ⟨W, hW⟩ := hflag.1
      exact ⟨W, Finset.mem_union_left _ hW⟩
    · intro s hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact hflag.2.1 s hs
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hs
        have hWvalid := hflag.2.1 W hW
        have hWnerve := largeFaceSubfaces_mem_nerve p a W hWvalid.1 hWvalid.2
        have hdata := (mem_largeFaceNerve_iff p a (largeFaceSubfaces p a W)).mp hWnerve
        have hlast : lastVertex (largeFaceSubfaces p a W) ∈
            largeFaceSubfaces p a W := by
          rw [lastVertex_of_nonempty _ hdata.1]
          exact Finset.max'_mem _ hdata.1
        rcases (mem_largeFaceSubfaces p a W _).mp hlast with hEq | hsmall
        · simpa [hEq] using hWvalid
        · exact ⟨hsmall.2.1, hsmall.2.2⟩
    · intro v hv
      obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hv
      rcases Finset.mem_union.mp hs with hs | hs
      · exact hmax s hs hvs
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hs
        have hWvalid := hflag.2.1 W hW
        have hWnerve := largeFaceSubfaces_mem_nerve p a W hWvalid.1 hWvalid.2
        have hdata := (mem_largeFaceNerve_iff p a (largeFaceSubfaces p a W)).mp hWnerve
        have hlast : lastVertex (largeFaceSubfaces p a W) ∈
            largeFaceSubfaces p a W := by
          rw [lastVertex_of_nonempty _ hdata.1]
          exact Finset.max'_mem _ hdata.1
        rcases (mem_largeFaceSubfaces p a W _).mp hlast with hEq | hsmall
        · have hvW : v ∈ W := by simpa [hEq] using hvs
          exact hmax W hW hvW
        · exact hmax W hW (hsmall.1 hvs)
    · exact hUvalid.1
  change C.image id ∪ C.image (fun W => lastVertex (largeFaceSubfaces p a W)) ∈
    (largeFaceNerveBifiltration p).toFun a
  change labels ∈ (largeFaceNerveBifiltration p).toFun a at hlabels
  simpa [Finset.image_id, labels] using hlabels

private theorem faceUnion_inclusion_homology_eq {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (n : ℕ) :
    simplicialHomologyMap R (largeFaceUnionVertexMap p a) n ≫
        simplicialHomologyIncl R
          (subdivision_openCech_le_largeFaceNerve p a) n =
      (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom := by
  have h := TDA.Simplicial.Contiguous.simplicialHomologyMap_eq R
    (faceUnion_inclusion_contiguous_lastVertex p a) n
  rw [simplicialHomologyMap_comp, simplicialHomologyMap_inclusion] at h
  change simplicialHomologyMap R (largeFaceUnionVertexMap p a) n ≫
      simplicialHomologyIncl R (subdivision_openCech_le_largeFaceNerve p a) n =
    (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom at h
  exact h

private theorem inclusion_subfaces_homology_eq {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (n : ℕ) :
    simplicialHomologyIncl R
        (subdivision_openCech_le_largeFaceNerve p a) n =
      simplicialHomologyMap R (largeFaceSubfacesVertexMap p a) n ≫
        (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom := by
  have h := TDA.Simplicial.Contiguous.simplicialHomologyMap_eq R
    (inclusion_contiguous_subfaces_lastVertex p a) n
  change simplicialHomologyMap R (inclusionVertexMap
      (subdivision_openCech_le_largeFaceNerve p a)) n =
    simplicialHomologyMap R
      (VertexMap.comp (largeFaceSubfacesVertexMap p a)
        (lastVertexMap (TDA.Topology.nerve (largeFaceCover p a)))) n at h
  rw [simplicialHomologyMap_inclusion, simplicialHomologyMap_comp] at h
  change simplicialHomologyIncl R (subdivision_openCech_le_largeFaceNerve p a) n =
      simplicialHomologyMap R (largeFaceSubfacesVertexMap p a) n ≫
        (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom at h
  exact h

private noncomputable def cechLargeFaceNerveComponentIso {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (n : ℕ) :
    simplicialHomology (subdivision (openCech p (radius a)) (mass a)) R n ≅
      simplicialHomology (TDA.Topology.nerve (largeFaceCover p a)) R n where
  hom := simplicialHomologyIncl R (subdivision_openCech_le_largeFaceNerve p a) n
  inv := (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).inv ≫
    simplicialHomologyMap R (largeFaceUnionVertexMap p a) n
  hom_inv_id := by
    have hgi : simplicialHomologyMap R (largeFaceSubfacesVertexMap p a) n ≫
        simplicialHomologyMap R (largeFaceUnionVertexMap p a) n =
        𝟙 (simplicialHomology
          (subdivision (openCech p (radius a)) (mass a)) R n) := by
      calc
        _ = simplicialHomologyMap R
            (VertexMap.comp (largeFaceSubfacesVertexMap p a)
              (largeFaceUnionVertexMap p a)) n :=
              (simplicialHomologyMap_comp R _ _ n).symm
        _ = simplicialHomologyMap R
            (VertexMap.id (subdivision (openCech p (radius a)) (mass a))) n := by
              rw [largeFaceSubfaces_union_map_eq_id]
        _ = 𝟙 _ := simplicialHomologyMap_id R _ n
    calc
      _ = (simplicialHomologyMap R (largeFaceSubfacesVertexMap p a) n ≫
            (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom) ≫
            (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).inv ≫
            simplicialHomologyMap R (largeFaceUnionVertexMap p a) n := by
        rw [inclusion_subfaces_homology_eq]
      _ = (simplicialHomologyMap R (largeFaceSubfacesVertexMap p a) n ≫
            ((barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom ≫
              (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).inv)) ≫
            simplicialHomologyMap R (largeFaceUnionVertexMap p a) n := by
        simp [Category.assoc]
      _ = 𝟙 _ := by
        rw [(barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom_inv_id]
        exact hgi
  inv_hom_id := by
    calc
      _ = (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).inv ≫
            (simplicialHomologyMap R (largeFaceUnionVertexMap p a) n ≫
              simplicialHomologyIncl R
                (subdivision_openCech_le_largeFaceNerve p a) n) := by
        simp [Category.assoc]
      _ = (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).inv ≫
            (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).hom := by
        rw [faceUnion_inclusion_homology_eq]
      _ = 𝟙 _ :=
        (barycentricHomologyIso R (TDA.Topology.nerve (largeFaceCover p a)) n).inv_hom_id

/-- The natural Čech-to-large-face-nerve homology map is an isomorphism at
every mass-radius index and in every degree. -/
theorem cechHomologyToLargeFaceNerve_isIso {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (a : Index) (n : ℕ) :
    IsIso ((cechHomologyToLargeFaceNerve R p n).app a) := by
  change IsIso (cechLargeFaceNerveComponentIso R p a n).hom
  infer_instance

/-- The Čech-to-large-face-nerve comparison is a natural isomorphism of
homology persistence modules. -/
noncomputable def cechHomologyToLargeFaceNerveIso {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (n : ℕ) :
    simplicialHomologyPModule R (cechBifiltration p) n ≅
      simplicialHomologyPModule R (largeFaceNerveBifiltration p) n :=
  NatIso.ofComponents
    (fun a => cechLargeFaceNerveComponentIso R p a n)
    (by
      intro a b f
      exact (cechHomologyToLargeFaceNerve R p n).naturality f)

end TDA.Persistence.SubdivisionRips

end
