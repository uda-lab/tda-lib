import TDA.Persistence.SublevelDiagram
import TDA.Filtration.OrderingEquivalent

/-!
# Transport of actual diagrams across ordering-equivalent face filters

The two laws relabel attained endpoint occurrences and preserve essential top.
Strictness is required only on attained source grades; there is no arbitrary
ambient-threshold naturality or global diagram map.
-/

set_option autoImplicit false

universe u v w
namespace TDA.Persistence
open TDA.Simplicial TDA.Filtration CategoryTheory

variable {V : Type u} [LinearOrder V]
variable (k : Type u) [Field k]
variable {α : Type v} {β : Type w} [LinearOrder α] [LinearOrder β]
variable {K : PreAbstractSimplicialComplex V}
variable [Fintype (TDA.Simplicial.TotalFace K)]

omit [LinearOrder V] in
private theorem critical_set_eq_range (f : FilterFunction K α) :
    (f.criticalValues : Set α) = Set.range f.value := by
  ext a
  exact f.mem_criticalValues a

private noncomputable def criticalRangeIso (f : FilterFunction K α) :
    f.criticalValues ≃o Set.range f.value :=
  OrderIso.setCongr (f.criticalValues : Set α) (Set.range f.value) (critical_set_eq_range f)

private noncomputable def criticalIso (f : FilterFunction K α)
    (g : FilterFunction K β) (e : Set.range f.value ≃o Set.range g.value) :
    f.criticalValues ≃o g.criticalValues :=
  (criticalRangeIso f).trans (e.trans (criticalRangeIso g).symm)

omit [LinearOrder V] in
private theorem critical_card_eq (f : FilterFunction K α)
    (g : FilterFunction K β) (e : Set.range f.value ≃o Set.range g.value) :
    f.criticalValues.card = g.criticalValues.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (criticalIso f g e).toEquiv

private def enumeration (f : FilterFunction K α) (N : ℕ)
    (hN : f.criticalValues.card = N) : Fin N ↪o α :=
  f.criticalValues.orderEmbOfFin hN

private def alignedFiltration (f : FilterFunction K α) (N : ℕ)
    (hN : f.criticalValues.card = N) : SimplicialFiltration (Fin N) V :=
  TDA.Filtration.reindex (enumeration f N hN).toOrderHom f.sublevelFiltration

private noncomputable instance aligned_finiteDimensional
    (f : FilterFunction K α) (N : ℕ) (hN : f.criticalValues.card = N)
    (n : ℕ) (i : Fin N) :
    FiniteDimensional k ((simplicialHomologyPModule k
      (alignedFiltration f N hN) n).obj i) := by
  subst N
  exact gradeHomology_finiteDimensional k f n i

private def endpointPoint {N : ℕ} (v : Fin N → α) (I : FiniteInterval N) :
    α × WithTop α :=
  (v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
   if hd : I.death < N then (v ⟨I.death, hd⟩ : WithTop α) else ⊤)

private theorem diagram_aligned (f : FilterFunction K α) (N : ℕ)
    (hN : f.criticalValues.card = N) (n : ℕ) :
    (dgm k f n).points =
      (rankBarcode (simplicialHomologyPModule k (alignedFiltration f N hN) n)).map
        (endpointPoint (enumeration f N hN)) := by
  subst N
  rfl

omit [LinearOrder V] in
private theorem enumeration_corresponds (f : FilterFunction K α)
    (g : FilterFunction K β) (N : ℕ)
    (hf : f.criticalValues.card = N) (hg : g.criticalValues.card = N)
    (e : Set.range f.value ≃o Set.range g.value) (i : Fin N) :
    (e ⟨enumeration f N hf i,
      (f.mem_criticalValues _).1 (Finset.orderEmbOfFin_mem _ hf i)⟩).val =
      enumeration g N hg i := by
  let F : Fin N → β := fun j =>
    (e ⟨enumeration f N hf j,
      (f.mem_criticalValues _).1 (Finset.orderEmbOfFin_mem _ hf j)⟩).val
  have hmem (j : Fin N) : F j ∈ g.criticalValues :=
    (g.mem_criticalValues _).2 (e _).property
  have hmono : StrictMono F := by
    intro a b hab
    exact e.strictMono ((enumeration f N hf).strictMono hab)
  exact congrFun (Finset.orderEmbOfFin_unique hg hmem hmono) i

private theorem inclusion_square {A B A' B' : PreAbstractSimplicialComplex V}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') (n : ℕ) :
    simplicialHomologyIncl k h n ≫
        eqToHom (congrArg (fun C => simplicialHomology C k n) hB) =
      eqToHom (congrArg (fun C => simplicialHomology C k n) hA) ≫
        simplicialHomologyIncl k h' n := by
  subst A'
  subst B'
  simp

private theorem inclusion_rank_eq {A B A' B' : PreAbstractSimplicialComplex V}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') (n : ℕ) :
    Module.finrank k (LinearMap.range (simplicialHomologyIncl k h n).hom) =
      Module.finrank k (LinearMap.range (simplicialHomologyIncl k h' n).hom) := by
  subst A'
  subst B'
  rfl

private theorem common_at_card (f : FilterFunction K α) (g : FilterFunction K β)
    (hfg : OrderingEquivalent f g) (N : ℕ)
    (hf : f.criticalValues.card = N) (hg : g.criticalValues.card = N)
    (e : Set.range f.value ≃o Set.range g.value)
    (he : ∀ s : TotalFace K, (e ⟨f.value s, ⟨s, rfl⟩⟩).val = g.value s)
    (n : ℕ) :
    ∃ E : Multiset (TotalFace K × Option (TotalFace K)),
      (dgm k f n).points = E.map (fun p =>
        (f.value p.1, p.2.elim (⊤ : WithTop α) (fun t => (f.value t : WithTop α)))) ∧
      (dgm k g n).points = E.map (fun p =>
        (g.value p.1, p.2.elim (⊤ : WithTop β) (fun t => (g.value t : WithTop β)))) := by
  classical
  have attained (i : Fin N) : ∃ s : TotalFace K, f.value s = enumeration f N hf i :=
    (f.mem_criticalValues _).1 (Finset.orderEmbOfFin_mem _ hf i)
  let face : Fin N → TotalFace K := fun i => Classical.choose (attained i)
  have hface (i : Fin N) : f.value (face i) = enumeration f N hf i :=
    Classical.choose_spec (attained i)
  have htarget (i : Fin N) : g.value (face i) = enumeration g N hg i := by
    rw [← he (face i)]
    have hs : (⟨f.value (face i), ⟨face i, rfl⟩⟩ : Set.range f.value) =
        ⟨enumeration f N hf i,
          (f.mem_criticalValues _).1 (Finset.orderEmbOfFin_mem _ hf i)⟩ :=
      Subtype.ext (hface i)
    rw [hs]
    exact enumeration_corresponds f g N hf hg e i
  have hstage (i : Fin N) : alignedFiltration f N hf i = alignedFiltration g N hg i := by
    change f.sublevel (enumeration f N hf i) = g.sublevel (enumeration g N hg i)
    rw [← hface i, ← htarget i]
    exact hfg.sublevel_eq (face i)
  have hsquare (i j : Fin N) (hij : i ≤ j) :=
    inclusion_square k (hstage i) (hstage j)
      ((alignedFiltration f N hf).monotone hij)
      ((alignedFiltration g N hg).monotone hij) n
  have hbarcode :
      rankBarcode (simplicialHomologyPModule k (alignedFiltration f N hf) n) =
        rankBarcode (simplicialHomologyPModule k (alignedFiltration g N hg) n) := by
    apply (rankBarcode_eq_iff _ _).2
    intro i j hij
    exact inclusion_rank_eq k (hstage i) (hstage j)
      ((alignedFiltration f N hf).monotone hij)
      ((alignedFiltration g N hg).monotone hij) n
  let witness : FiniteInterval N → TotalFace K × Option (TotalFace K) := fun I =>
    (face ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
      if hd : I.death < N then some (face ⟨I.death, hd⟩) else none)
  let B := rankBarcode (simplicialHomologyPModule k (alignedFiltration f N hf) n)
  refine ⟨B.map witness, ?_, ?_⟩
  · rw [diagram_aligned k f N hf n, Multiset.map_map]
    apply congrArg (fun t => B.map t)
    funext I
    dsimp [endpointPoint, witness]
    split_ifs <;> simp [hface]
  · rw [diagram_aligned k g N hg n, ← hbarcode, Multiset.map_map]
    apply congrArg (fun t => B.map t)
    funext I
    dsimp [endpointPoint, witness]
    split_ifs <;> simp [htarget]

/-- Ordering-equivalent actual filters share a multiset of face-witnessed endpoint
occurrences. `none` witnesses essential death, while every finite endpoint is attained. -/
theorem dgm_common_face_endpoints_of_orderingEquivalent
    (f : TDA.Filtration.FilterFunction K α)
    (g : TDA.Filtration.FilterFunction K β)
    (hfg : TDA.Filtration.OrderingEquivalent f g) (n : ℕ) :
    ∃ E : Multiset (TDA.Simplicial.TotalFace K ×
        Option (TDA.Simplicial.TotalFace K)),
      (dgm k f n).points = E.map (fun p =>
        (f.value p.1,
          p.2.elim (⊤ : WithTop α) (fun t => (f.value t : WithTop α)))) ∧
      (dgm k g n).points = E.map (fun p =>
        (g.value p.1,
          p.2.elim (⊤ : WithTop β) (fun t => (g.value t : WithTop β)))) := by
  obtain ⟨e, he⟩ := (orderingEquivalent_iff_exists_rangeOrderIso f g).1 hfg
  exact common_at_card k f g hfg f.criticalValues.card rfl
    (critical_card_eq f g e).symm e he n

/-- A map strictly increasing on attained source grades transports the actual point
multiset and fixes essential death. No behavior away from attained grades is assumed. -/
theorem dgm_points_map_of_strictMonoOn
    (f : TDA.Filtration.FilterFunction K α)
    (g : TDA.Filtration.FilterFunction K β)
    (φ : α → β) (hφ : StrictMonoOn φ (Set.range f.value))
    (hvalue : ∀ s : TDA.Simplicial.TotalFace K, g.value s = φ (f.value s))
    (n : ℕ) :
    (dgm k g n).points = (dgm k f n).points.map
      (fun p => (φ p.1, WithTop.map φ p.2)) := by
  have hfg : OrderingEquivalent f g := by
    intro s t
    rw [hvalue s, hvalue t]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (hφ ⟨s, rfl⟩ ⟨t, rfl⟩ hlt).le
      · exact (congrArg φ heq).le
    · intro h
      by_contra hn
      exact (not_lt_of_ge h) (hφ ⟨t, rfl⟩ ⟨s, rfl⟩ (lt_of_not_ge hn))
  obtain ⟨E, hf, hg⟩ := dgm_common_face_endpoints_of_orderingEquivalent k f g hfg n
  rw [hf, hg, Multiset.map_map]
  apply congrArg (fun t => E.map t)
  funext p
  rcases p with ⟨s, d⟩
  cases d <;> simp [hvalue]

end TDA.Persistence
