import TDA.Persistence.SublevelConstructible
import TDA.Persistence.RankProjective
import TDA.Persistence.EssentialVanishing
import TDA.Persistence.RankBarcodeIso
import TDA.Simplicial.H0Augmentation

/-!
# Reduced degree-zero Rips diagrams

Reduced degree-zero persistence is the kernel of the ordinary H₀ augmentation. On
finite Rips samples, the augmentation splits off the single class born at time zero;
the rank barcode theorem identifies the remaining diagram, with multiplicities, as
the finite part of the ordinary H₀ diagram.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace TDA.Persistence.Rips

open CategoryTheory CategoryTheory.Limits TDA.Filtration TDA.Simplicial
open TDA.Persistence.FiniteConstructible

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]

/-! ## The augmentation on ordinary simplicial H₀ -/

/-- A chosen target vertex used to identify every singleton complex with a point. -/
noncomputable def h0Basepoint [Nonempty V] : V := Classical.choice ‹Nonempty V›

/-- Collapse every vertex to the sole vertex of the point complex. -/
noncomputable def pointCollapseVertexMap (K : PreAbstractSimplicialComplex V) (v₀ : V) :
    VertexMap K (TDA.Filtration.singletonFace v₀) where
  toFun := fun _ => v₀
  map_face := by
    classical
    letI : DecidableEq V := Classical.decEq V
    intro s hs
    have hsne : s.Nonempty := (K.isRelLowerSet_faces hs).1
    apply (TDA.Filtration.mem_singletonFace_iff v₀ _).2
    ext x
    constructor
    · intro hx
      simp only [Finset.mem_image] at hx
      obtain ⟨v, _, rfl⟩ := hx
      simp
    · intro hx
      have hx0 : x = v₀ := by simpa using hx
      subst x
      obtain ⟨v, hv⟩ := hsne
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- The ordinary H₀ augmentation is induced by the collapse to a point. -/
noncomputable def zeroHomologyCoefficientSum
    [Nonempty V] (K : PreAbstractSimplicialComplex V) :
    simplicialHomology K k 0 →ₗ[k] k :=
  (simplicialSingletonH0Equiv k (h0Basepoint (V := V))).toLinearMap.comp
    (simplicialHomologyMap k (pointCollapseVertexMap K (h0Basepoint (V := V))) 0).hom

/-- Collapse-to-a-point augmentations commute with every simplicial inclusion. -/
theorem zeroHomologyCoefficientSum_natural
    [Nonempty V] {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) :
    (zeroHomologyCoefficientSum k L).comp (simplicialHomologyIncl k h 0).hom =
      zeroHomologyCoefficientSum k K := by
  have hcompose :
      VertexMap.comp (inclusionVertexMap h)
          (pointCollapseVertexMap L (h0Basepoint (V := V))) =
        pointCollapseVertexMap K (h0Basepoint (V := V)) := by
    apply VertexMap.ext
    intro v
    rfl
  have hmap := simplicialHomologyMap_comp k (inclusionVertexMap h)
    (pointCollapseVertexMap L (h0Basepoint (V := V))) 0
  rw [hcompose, simplicialHomologyMap_inclusion] at hmap
  have hmapHom := congrArg (fun f => f.hom) hmap
  simp only [ModuleCat.hom_comp] at hmapHom
  simp only [zeroHomologyCoefficientSum]
  rw [LinearMap.comp_assoc, ← hmapHom]

/-- A vertex class maps to its coefficient under the augmentation. -/
theorem zeroHomologyCoefficientSum_vertex
    [Nonempty V] (K : PreAbstractSimplicialComplex V) (σ : Face K 0) (a : k) :
    zeroHomologyCoefficientSum k K
      (simplicialHomologyClass k K 0 (a • zeroVertexCycle K k σ)) = a := by
  let v₀ := h0Basepoint (V := V)
  let P := TDA.Filtration.singletonFace v₀
  have hface : vertexImageFace (pointCollapseVertexMap K v₀) σ
      (fun i j _ => Fin.ext (by omega)) = singletonVertex v₀ :=
    Subsingleton.elim _ _
  have hchain : vertexChainMap k (pointCollapseVertexMap K v₀) 0
      (a • zeroVertexCycle K k σ : Chain K k 0) =
        (a • zeroVertexCycle P k (singletonVertex v₀) : Chain P k 0) := by
    change vertexChainMap k (pointCollapseVertexMap K v₀) 0
        (a • Finsupp.single σ (1 : k)) =
      a • Finsupp.single (singletonVertex v₀) (1 : k)
    rw [map_smul, vertexChainMap_vertex, hface]
  rw [zeroHomologyCoefficientSum, LinearMap.comp_apply]
  have hclass := simplicialHomologyMap_class (R := k) (f := pointCollapseVertexMap K v₀)
    (n := 0) (z := a • zeroVertexCycle K k σ)
    (w := a • zeroVertexCycle P k (singletonVertex v₀)) hchain
  have hcycle : (a • zeroVertexCycle P k (singletonVertex v₀) : simplicialCycles P k 0) =
      ⟨Finsupp.single (singletonVertex v₀) a, by
        rw [simplicialCycles_zero]
        trivial⟩ := by
    apply Subtype.ext
    simp [zeroVertexCycle, Finsupp.smul_single]
  rw [hclass]
  rw [hcycle]
  exact simplicialSingletonH0Equiv_class k v₀ a

/-! ## Rips augmentation and its kernel -/

/-- The natural augmentation from ordinary sublevel H₀ to the constant coefficient module,
induced at every threshold by collapsing the sublevel to a point. -/
noncomputable def sublevelH0Augmentation [Nonempty V] (d : MetricSpace V) :
    sublevelModule k (TDA.Filtration.Rips.filter d) 0 ⟶
      (Functor.const ℝ).obj (ModuleCat.of k k) where
  app t := ModuleCat.ofHom
    (zeroHomologyCoefficientSum k ((TDA.Filtration.Rips.filter d).sublevel t))
  naturality s t f := by
    have hnat := zeroHomologyCoefficientSum_natural k
      ((TDA.Filtration.Rips.filter d).sublevel_mono (leOfHom f))
    apply ModuleCat.hom_ext
    simpa [sublevelModule, TDA.Filtration.FilterFunction.sublevelFiltration_apply,
      simplicialHomologyPModule, Functor.const_obj_map,
      ModuleCat.hom_comp, ModuleCat.ofHom_hom, Category.comp_id] using hnat

/-- The reduced sublevel H₀ module is the actual categorical kernel of augmentation. -/
noncomputable def reducedSublevelH0Module [Nonempty V] (d : MetricSpace V) :
    PModule.{u,0,u} k ℝ := kernel (sublevelH0Augmentation k d)

/-- Every critical fiber of the reduced Rips H₀ module is finite dimensional. -/
theorem reducedSublevelH0_finiteDimensional [Fintype V] [Nonempty V] (d : MetricSpace V)
    (i : Fin (TDA.Filtration.Rips.filter d).criticalValues.card) :
    FiniteDimensional k
      ((reducedSublevelH0Module k d).obj ((TDA.Filtration.Rips.filter d).criticalValue i)) := by
  let f := TDA.Filtration.Rips.filter d
  letI : FiniteDimensional k ((sublevelModule k f 0).obj (f.criticalValue i)) :=
    sublevelModule_finiteDimensional k 0 f i
  exact RankKernel.finiteDimensional (sublevelH0Augmentation k d) (f.criticalValue i)

/-- The reduced Rips H₀ diagram is the finite-constructible diagram of the actual
augmentation kernel. -/
noncomputable def reducedSublevelH0Diagram [Fintype V] [Nonempty V] (d : MetricSpace V) : Diagram ℝ :=
  FiniteConstructible.moduleDiagram (TDA.Filtration.Rips.filter d).criticalValue
    (reducedSublevelH0Module k d) (reducedSublevelH0_finiteDimensional k d)

private theorem ripsZeroCriticalValue_mem [Fintype V] [Nonempty V]
    (d : MetricSpace V) :
    (0 : ℝ) ∈ (TDA.Filtration.Rips.filter d).criticalValues := by
  obtain ⟨v⟩ := ‹Nonempty V›
  apply (TDA.Filtration.Rips.filter d).mem_criticalValues 0 |>.2
  refine ⟨⟨{v}, by simp⟩, ?_⟩
  simp [TDA.Filtration.Rips.filter, TDA.Filtration.Rips.diameter_singleton]

private theorem ripsCriticalValue_nonneg [Fintype V] (d : MetricSpace V)
    (i : Fin (TDA.Filtration.Rips.filter d).criticalValues.card) :
    0 ≤ (TDA.Filtration.Rips.filter d).criticalValue i := by
  let f := TDA.Filtration.Rips.filter d
  obtain ⟨s, hs⟩ := (f.mem_criticalValues (f.criticalValue i)).1 (f.criticalValue_mem i)
  rw [← hs, TDA.Filtration.Rips.filter_value]
  exact TDA.Filtration.Rips.diameter_nonneg d s.1

/-- Every nonnegative Rips sublevel contains a vertex, so its H₀ augmentation is onto. -/
private theorem sublevelH0Augmentation_surjective [Nonempty V]
    (d : MetricSpace V) {t : ℝ} (ht : 0 ≤ t) :
    Function.Surjective ((sublevelH0Augmentation k d).app t).hom := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  let K := (TDA.Filtration.Rips.filter d).sublevelFiltration t
  have hvertex : {v} ∈ K := by
    change {v} ∈ (TDA.Filtration.Rips.filter d).sublevel t
    rw [TDA.Filtration.Rips.mem_sublevel_iff]
    refine ⟨by simp, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    simpa using ht
  let σ : Face K 0 := ⟨{v}, hvertex, by simp⟩
  intro a
  refine ⟨simplicialHomologyClass k K 0 (a • zeroVertexCycle K k σ), ?_⟩
  have hcollapse : (sublevelH0Augmentation k d).app t =
      ModuleCat.ofHom (zeroHomologyCoefficientSum k K) := by
    rfl
  rw [hcollapse]
  change zeroHomologyCoefficientSum k K
    (simplicialHomologyClass k K 0 (a • zeroVertexCycle K k σ)) = a
  exact zeroHomologyCoefficientSum_vertex k K σ a

private theorem sublevelH0Augmentation_rankExact [Fintype V] [Nonempty V]
    (d : MetricSpace V) :
    IsRankExact
      (kernel.ι (reindexNatTrans (TDA.Filtration.Rips.filter d).criticalValue.toOrderHom
        (sublevelH0Augmentation k d)))
      (reindexNatTrans (TDA.Filtration.Rips.filter d).criticalValue.toOrderHom
        (sublevelH0Augmentation k d)) := by
  let f := TDA.Filtration.Rips.filter d
  let c := f.criticalValue
  let π := reindexNatTrans c.toOrderHom (sublevelH0Augmentation k d)
  letI : ∀ i, FiniteDimensional k
      ((reindex c.toOrderHom (sublevelModule k f 0)).obj i) := by
    intro i
    change FiniteDimensional k ((sublevelModule k f 0).obj (c i))
    exact sublevelModule_finiteDimensional k 0 f i
  apply RankKernel.rankExact π
  · intro i
    exact sublevelH0Augmentation_surjective k d (ripsCriticalValue_nonneg d i)
  · intro a b hab n hn
    have hn0 : n = 0 := by
      change n = 0 at hn
      exact hn
    subst n
    refine ⟨0, ?_, ?_⟩
    · exact map_zero _
    · exact map_zero _

private theorem ripsFirstCriticalValue_eq_zero [Fintype V] [Nonempty V]
    (d : MetricSpace V) :
    (TDA.Filtration.Rips.filter d).criticalValue
      ⟨0, Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩⟩ = 0 := by
  let f := TDA.Filtration.Rips.filter d
  let c := f.criticalValue
  obtain ⟨v⟩ := ‹Nonempty V›
  let s : TotalFace (TDA.Filtration.Rips.fullComplex V) := ⟨{v}, by simp⟩
  obtain ⟨j, hj⟩ := f.exists_criticalValue_eq s
  have hzero : c j = 0 := by
    rw [hj, TDA.Filtration.Rips.filter_value, TDA.Filtration.Rips.diameter_singleton]
  have hnonneg : 0 ≤ c ⟨0, Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩⟩ :=
    ripsCriticalValue_nonneg d _
  have hfirst : (⟨0, Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩⟩ :
      Fin f.criticalValues.card) ≤ j := Fin.le_def.mpr (Nat.zero_le _)
  have hle : c ⟨0, Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩⟩ ≤ 0 := by
    calc
      c ⟨0, Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩⟩ ≤ c j := c.monotone hfirst
      _ = 0 := hzero
  exact le_antisymm hle hnonneg

private def zeroBornEssentialInterval (n : ℕ) (hn : 0 < n) : FiniteInterval n where
  birth := 0
  death := n
  birth_lt_death := hn
  death_le_size := le_rfl

private theorem finitePart_add_local {α : Type u} [LinearOrder α]
    (s t : Multiset (α × WithTop α)) :
    finitePart (s + t) = finitePart s + finitePart t := by
  exact Multiset.filterMap_add _ _ _

private theorem finitePart_top_singleton {α : Type u} [LinearOrder α] (b : α) :
    finitePart ({(b, (⊤ : WithTop α))} : Multiset (α × WithTop α)) = 0 := by
  rw [finitePart]
  rw [← Multiset.cons_zero]
  change Multiset.filterMap (fun p : α × WithTop α =>
    match p.2 with
    | none => none
    | some q => some (p.1, q)) ((b, (⊤ : WithTop α)) ::ₘ 0) = 0
  rw [Multiset.filterMap_cons_none _ _ (by rfl)]
  rfl

/-- RankBarcode of the actual reduced kernel on the critical grid. -/
noncomputable def reducedCriticalH0Barcode [Fintype V] [Nonempty V] (d : MetricSpace V) :
    Multiset (FiniteInterval (TDA.Filtration.Rips.filter d).criticalValues.card) := by
  let f := TDA.Filtration.Rips.filter d
  let c := f.criticalValue
  let π := reindexNatTrans c.toOrderHom (sublevelH0Augmentation k d)
  letI : ∀ i, FiniteDimensional k
      ((reindex c.toOrderHom (sublevelModule k f 0)).obj i) := by
    intro i
    exact sublevelModule_finiteDimensional k 0 f i
  letI : ∀ i, FiniteDimensional k ((kernel π).obj i) := by
    intro i
    exact RankKernel.finiteDimensional π i
  exact rankBarcode (kernel π)

/-- On the Rips critical grid, ordinary H₀ has exactly one more barcode occurrence
than the genuine reduced module: the interval from zero to the essential tail. -/
private theorem ripsH0CriticalBarcode_decomposition [Fintype V] [Nonempty V]
    (d : MetricSpace V)
    [∀ i, FiniteDimensional k
      ((reindex (TDA.Filtration.Rips.filter d).criticalValue.toOrderHom
        (sublevelModule k (TDA.Filtration.Rips.filter d) 0)).obj i)] :
    rankBarcode (reindex (TDA.Filtration.Rips.filter d).criticalValue.toOrderHom
      (sublevelModule k (TDA.Filtration.Rips.filter d) 0)) =
      reducedCriticalH0Barcode k d +
        {zeroBornEssentialInterval
          (TDA.Filtration.Rips.filter d).criticalValues.card
          (Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩)} := by
  classical
  let f := TDA.Filtration.Rips.filter d
  let c := f.criticalValue
  let M := reindex c.toOrderHom (sublevelModule k f 0)
  let N := reindex c.toOrderHom ((Functor.const ℝ).obj (ModuleCat.of k k))
  let π := reindexNatTrans c.toOrderHom (sublevelH0Augmentation k d)
  let K := kernel π
  let hn : 0 < f.criticalValues.card := Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩
  let I₀ := zeroBornEssentialInterval f.criticalValues.card hn
  let B := reducedCriticalH0Barcode k d + {I₀}
  letI : ∀ i, FiniteDimensional k (M.obj i) := by
    intro i
    change FiniteDimensional k ((sublevelModule k f 0).obj (c i))
    exact sublevelModule_finiteDimensional k 0 f i
  letI : ∀ i, FiniteDimensional k (K.obj i) := by
    intro i
    exact RankKernel.finiteDimensional π i
  have hExact := sublevelH0Augmentation_rankExact k d
  have hbarcode : rankBarcode M = rankBarcode (barcodeModule (k := k) B) := by
    apply (rankBarcode_eq_iff M (barcodeModule (k := k) B)).2
    intro i j hij
    have hrank := hExact.rank_add hij
    have hsum : structureMapRank M i j hij = structureMapRank K i j hij + 1 := by
      change Module.finrank k (LinearMap.range (structureMapLinear M hij)) =
        Module.finrank k (LinearMap.range (structureMapLinear K hij)) + 1
      have hrank' := hrank
      change Module.finrank k (LinearMap.range (structureMapLinear M hij)) =
        Module.finrank k (LinearMap.range (structureMapLinear K hij)) +
          Module.finrank k (LinearMap.range (structureMapLinear N hij)) at hrank'
      have hdim : Module.finrank k
          (LinearMap.range (structureMapLinear N hij)) = 1 := by
        rw [structureMapLinear_reindex]
        simp only [N, structureMapLinear, structureMap, Functor.const_obj_map,
          ModuleCat.hom_id]
        change Module.finrank k
          (LinearMap.range (LinearMap.id : k →ₗ[k] k)) = 1
        rw [LinearMap.range_id, finrank_top]
        exact Module.finrank_self k
      rw [hdim] at hrank'
      exact hrank'
    have hcount : B.countP (fun I : FiniteInterval f.criticalValues.card =>
        I.birth ≤ i.val ∧ j.val < I.death) = structureMapRank K i j hij + 1 := by
      dsimp [B, reducedCriticalH0Barcode, zeroBornEssentialInterval]
      rw [Multiset.countP_add]
      have hI : (0 : ℕ) ≤ i.val ∧ j.val < f.criticalValues.card := by
        constructor
        · exact Nat.zero_le _
        · exact j.isLt
      have hK := structureMapRank_rankBarcode K i j hij
      rw [rank_barcodeMap] at hK
      have hsingle :
          ({I₀} : Multiset (FiniteInterval f.criticalValues.card)).countP
              (fun I : FiniteInterval f.criticalValues.card =>
                I.birth ≤ i.val ∧ j.val < I.death) = 1 := by
        rw [← Multiset.cons_zero, Multiset.countP_cons_of_pos]
        · simp
        · simpa [I₀, zeroBornEssentialInterval] using hI
      rw [hK, hsingle]
    calc
      structureMapRank M i j hij = structureMapRank K i j hij + 1 := hsum
      _ = B.countP (fun I : FiniteInterval f.criticalValues.card =>
            I.birth ≤ i.val ∧ j.val < I.death) := hcount.symm
      _ = structureMapRank (barcodeModule (k := k) B) i j hij :=
        (rank_barcodeMap B i j hij).symm
  change rankBarcode M = _
  calc
    rankBarcode M =
        rankBarcode (barcodeModule (k := k) B) := hbarcode
    _ = B := rankBarcode_barcodeModule B
    _ = reducedCriticalH0Barcode k d +
          {zeroBornEssentialInterval f.criticalValues.card hn} := rfl

/-- The barcode split pushes to the actual finite-sample diagram: the sole summand
removed from reduced H₀ is the essential occurrence born at zero. -/
private theorem reducedSublevelH0Diagram_points_addEssential [Fintype V] [Nonempty V]
    (d : MetricSpace V) :
    (reducedSublevelH0Diagram k d).points + {(0, (⊤ : WithTop ℝ))} =
      (dgm k (TDA.Filtration.Rips.filter d) 0).points := by
  classical
  let f := TDA.Filtration.Rips.filter d
  let c := f.criticalValue
  let hn : 0 < f.criticalValues.card := Finset.card_pos.mpr ⟨0, ripsZeroCriticalValue_mem d⟩
  let I₀ := zeroBornEssentialInterval f.criticalValues.card hn
  letI : ∀ i, FiniteDimensional k
      ((reindex c.toOrderHom (sublevelModule k f 0)).obj i) := by
    intro i
    change FiniteDimensional k ((sublevelModule k f 0).obj (c i))
    exact sublevelModule_finiteDimensional k 0 f i
  letI : ∀ i, FiniteDimensional k
      ((reindex c.toOrderHom (reducedSublevelH0Module k d)).obj i) :=
    reducedSublevelH0_finiteDimensional k d
  have hgridIso :
      rankBarcode (reindex c.toOrderHom (reducedSublevelH0Module k d)) =
        reducedCriticalH0Barcode k d := by
    let π := reindexNatTrans c.toOrderHom (sublevelH0Augmentation k d)
    letI : ∀ i, FiniteDimensional k ((kernel π).obj i) := by
      intro i
      exact RankKernel.finiteDimensional π i
    exact rankBarcode_eq_of_iso (criticalKernelIso c (sublevelH0Augmentation k d))
  have hfirst := ripsFirstCriticalValue_eq_zero d
  have hI : RealBarcode.endpoints c I₀ = (0, (⊤ : WithTop ℝ)) := by
    dsimp [RealBarcode.endpoints, I₀, zeroBornEssentialInterval]
    rw [hfirst]
    simp
  rw [← moduleDiagram_sublevelModule k 0 f]
  simp only [reducedSublevelH0Diagram, FiniteConstructible.moduleDiagram,
    RealBarcode.ofIndexBars_points]
  rw [hgridIso, ripsH0CriticalBarcode_decomposition k d]
  rw [Multiset.map_add]
  rw [Multiset.map_singleton]
  rw [hI]

/-- The actual reduced degree-zero Rips diagram is exactly the finite part of the
ordinary degree-zero Rips diagram, including every finite-bar multiplicity. -/
theorem reducedSublevelH0Diagram_points_eq_finitePart [Fintype V] [Nonempty V]
    (d : MetricSpace V) :
    (reducedSublevelH0Diagram k d).points =
      (finitePart (dgm k (TDA.Filtration.Rips.filter d) 0).points).map
        (fun p => (p.1, (p.2 : WithTop ℝ))) := by
  classical
  have hpoints := reducedSublevelH0Diagram_points_addEssential k d
  have hfullEss := TDA.Persistence.Rips.card_essentialPart_dgm_zero (k := k) d
  have hessCard : (essentialPart (reducedSublevelH0Diagram k d).points).card = 0 := by
    have hc := congrArg (fun s => (essentialPart s).card) hpoints
    have hc' :
        (essentialPart (reducedSublevelH0Diagram k d).points).card +
            (essentialPart ({(0, (⊤ : WithTop ℝ))} : Multiset (ℝ × WithTop ℝ))).card = 1 := by
      simpa [essentialPart, Multiset.filterMap_add] using hc.trans hfullEss
    have hsingle :
        (essentialPart ({(0, (⊤ : WithTop ℝ))} : Multiset (ℝ × WithTop ℝ))).card = 1 := by
      rw [essentialPart]
      change (Multiset.filterMap (fun p : ℝ × WithTop ℝ =>
        match p.2 with
        | none => some p.1
        | some _ => none) ((0, (⊤ : WithTop ℝ)) ::ₘ 0)).card = 1
      rw [Multiset.filterMap_cons_some _ _ _ (by rfl)]
      simp
    rw [hsingle] at hc'
    omega
  have hess : essentialPart (reducedSublevelH0Diagram k d).points = 0 :=
    Multiset.card_eq_zero.mp hessCard
  have hparts := parts_reconstruct (reducedSublevelH0Diagram k d).points
  rw [hess, Multiset.map_zero, add_zero] at hparts
  have hfinite :
      finitePart (dgm k (TDA.Filtration.Rips.filter d) 0).points =
        finitePart (reducedSublevelH0Diagram k d).points := by
    rw [← hpoints, finitePart_add_local, finitePart_top_singleton, add_zero]
  calc
    (reducedSublevelH0Diagram k d).points =
        (finitePart (reducedSublevelH0Diagram k d).points).map
          (fun p => (p.1, (p.2 : WithTop ℝ))) := hparts.symm
    _ = (finitePart (dgm k (TDA.Filtration.Rips.filter d) 0).points).map
          (fun p => (p.1, (p.2 : WithTop ℝ))) := by rw [← hfinite]

/-- Erasing the essential `(0, ⊤)` occurrence from the full H₀ diagram leaves the
actual reduced H₀ diagram, with all finite-bar multiplicities preserved. -/
theorem reducedSublevelH0Diagram_points_eq_eraseEssential [Fintype V] [Nonempty V]
    (d : MetricSpace V) :
    (dgm k (TDA.Filtration.Rips.filter d) 0).points.erase (0, (⊤ : WithTop ℝ)) =
      (reducedSublevelH0Diagram k d).points := by
  rw [← reducedSublevelH0Diagram_points_addEssential k d]
  rw [Multiset.erase_add_right_pos
    (reducedSublevelH0Diagram k d).points (by simp)]
  simp

end TDA.Persistence.Rips
