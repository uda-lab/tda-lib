import TDA.Persistence.FinitePresentationHookCover
import TDA.Persistence.FiniteRankProjectiveClassification

/-!
# Rank-projectives among finitely presented real-coordinate modules

For a finitely presented module on real coordinate space, the actual finite-grid
hook cover splits when the module is rank projective. Full faithfulness of the
grid left Kan extension descends that splitting to the finite grid, where the
finite-poset classification applies. Isomorphic ambient finite hook sums also
have equal occurrence multiplicities: a common endpoint grid transports and
reflects their actual sum isomorphism.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GradedFree

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveClassification
open scoped TDA.Persistence

variable {k : Type u} [Field k] {n : ℕ}

private def embeddedCoverTag (G : CoordinateGrid n)
    (A : PModule.{u,0,u} k G.Point) :
    FiniteHookDeflation.Index A → RankProjectiveHookTag (Fin n → ℝ)
  | .inl t => .inl ⟨(G.embedding t.1.val.1, G.embedding t.1.val.2), by
      apply lt_of_le_of_ne
      · exact G.embedding.monotone t.1.property.le
      · intro h
        exact t.1.property.ne (G.embedding.injective h)⟩
  | .inr t => .inr (G.embedding t.1)

private noncomputable def embeddedCoverOccurrenceLanIso
    (G : CoordinateGrid n) (A : PModule.{u,0,u} k G.Point)
    (t : FiniteHookDeflation.Index A) :
    G.lan.obj (FiniteHookDeflation.family A t) ≅
      rankProjectiveHookModule (k := k) (embeddedCoverTag G A t) := by
  cases t with
  | inl t => exact G.hookLanIso t.1.val.1 t.1.val.2
  | inr t => exact G.infinityLanIso t.1

private noncomputable def rankProjectiveHookTagCoordinates
    (t : RankProjectiveHookTag (Fin n → ℝ)) (i : Fin n) : Finset ℝ := by
  classical
  cases t with
  | inl ab => exact {ab.val.1 i, ab.val.2 i}
  | inr a => exact {a i}

private noncomputable def hookSumCoordinateGrid {ι : Type} [Fintype ι]
    (T : ι → RankProjectiveHookTag (Fin n → ℝ)) : CoordinateGrid n := by
  classical
  exact fun i => Finset.univ.biUnion (fun j => rankProjectiveHookTagCoordinates (T j) i)

private def rankProjectiveHookTagInGrid (G : CoordinateGrid n)
    (t : RankProjectiveHookTag (Fin n → ℝ)) : Prop :=
  match t with
  | .inl ab =>
      (∀ i, ab.val.1 i ∈ G i) ∧ (∀ i, ab.val.2 i ∈ G i)
  | .inr a => ∀ i, a i ∈ G i

private theorem hookSumTag_mem_grid {ι : Type} [Fintype ι]
    (T : ι → RankProjectiveHookTag (Fin n → ℝ)) (j : ι) :
    rankProjectiveHookTagInGrid (hookSumCoordinateGrid T) (T j) := by
  classical
  cases ht : T j with
  | inl ab =>
      constructor
      · intro i
        apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        rw [ht]
        simp [rankProjectiveHookTagCoordinates]
      · intro i
        apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        rw [ht]
        simp [rankProjectiveHookTagCoordinates]
  | inr a =>
      intro i
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [ht]
      simp [rankProjectiveHookTagCoordinates]

private noncomputable def rankProjectiveHookTagIntoGrid (G : CoordinateGrid n)
    (t : RankProjectiveHookTag (Fin n → ℝ))
    (ht : rankProjectiveHookTagInGrid G t) :
    RankProjectiveHookTag G.Point := by
  classical
  cases t with
  | inl ab =>
      rcases ht with ⟨hb, hd⟩
      let b : G.Point := fun i => ⟨ab.val.1 i, hb i⟩
      let d : G.Point := fun i => ⟨ab.val.2 i, hd i⟩
      refine .inl ⟨(b, d), ?_⟩
      apply lt_iff_le_and_ne.mpr
      refine ⟨?_, ?_⟩
      · intro i
        exact ab.property.le i
      · intro hbd
        apply ab.property.ne
        exact funext fun i => congrArg Subtype.val (congrFun hbd i)
  | inr a =>
      exact .inr (fun i => ⟨a i, ht i⟩)

private noncomputable def rankProjectiveHookTagFromGrid (G : CoordinateGrid n)
    (t : RankProjectiveHookTag G.Point) : RankProjectiveHookTag (Fin n → ℝ) := by
  cases t with
  | inl ab => exact .inl ⟨(G.embedding ab.val.1, G.embedding ab.val.2),
      G.embedding.strictMono ab.property⟩
  | inr a => exact .inr (G.embedding a)

private theorem rankProjectiveHookTagFromGrid_intoGrid
    (G : CoordinateGrid n) (t : RankProjectiveHookTag (Fin n → ℝ))
    (ht : rankProjectiveHookTagInGrid G t) :
    rankProjectiveHookTagFromGrid G (rankProjectiveHookTagIntoGrid G t ht) = t := by
  cases t with
  | inl ab =>
      rcases ht with ⟨hb, hd⟩
      change Sum.inl
        ⟨(G.embedding (fun i => ⟨ab.val.1 i, hb i⟩),
          G.embedding (fun i => ⟨ab.val.2 i, hd i⟩)), _⟩ = Sum.inl ab
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · funext i
        rfl
      · funext i
        rfl
  | inr a =>
      change Sum.inr (G.embedding (fun i => ⟨a i, ht i⟩)) = Sum.inr a
      apply congrArg Sum.inr
      funext i
      rfl

private theorem rankProjectiveHookTagIntoGrid_eq_iff
    (G : CoordinateGrid n) {s t : RankProjectiveHookTag (Fin n → ℝ)}
    (hs : rankProjectiveHookTagInGrid G s) (ht : rankProjectiveHookTagInGrid G t) :
    rankProjectiveHookTagIntoGrid G s hs = rankProjectiveHookTagIntoGrid G t ht ↔
      s = t := by
  constructor
  · intro h
    have h' := congrArg (rankProjectiveHookTagFromGrid G) h
    rw [rankProjectiveHookTagFromGrid_intoGrid, rankProjectiveHookTagFromGrid_intoGrid] at h'
    exact h'
  · intro h
    cases h
    have hproof : hs = ht := Subsingleton.elim _ _
    cases hproof
    rfl

private noncomputable def rankProjectiveHookTagIntoGridLanIso
    (G : CoordinateGrid n) (t : RankProjectiveHookTag (Fin n → ℝ))
    (ht : rankProjectiveHookTagInGrid G t) :
    G.lan.obj
        (rankProjectiveHookModule (k := k) (rankProjectiveHookTagIntoGrid G t ht)) ≅
      rankProjectiveHookModule (k := k) t := by
  cases t with
  | inl ab =>
      rcases ht with ⟨hb, hd⟩
      let b : G.Point := fun i => ⟨ab.val.1 i, hb i⟩
      let d : G.Point := fun i => ⟨ab.val.2 i, hd i⟩
      have hbEmb : G.embedding b = ab.val.1 := by
        funext i
        rfl
      have hdEmb : G.embedding d = ab.val.2 := by
        funext i
        rfl
      have hSrc : rankProjectiveHookModule (k := k)
          (rankProjectiveHookTagIntoGrid G (Sum.inl ab) ⟨hb, hd⟩) =
          Hook.module (k := k) b d := by
        change Hook.module (k := k) b d = Hook.module (k := k) b d
        rfl
      have hTgt : Hook.module (k := k) (G.embedding b) (G.embedding d) =
          rankProjectiveHookModule (k := k) (Sum.inl ab) := by
        simp [rankProjectiveHookModule, hbEmb, hdEmb]
      exact (G.lan.mapIso (eqToIso hSrc)).trans
        ((G.hookLanIso (k := k) b d).trans (eqToIso hTgt))
  | inr a =>
      let b : G.Point := fun i => ⟨a i, ht i⟩
      have hbEmb : G.embedding b = a := by
        funext i
        rfl
      have hSrc : rankProjectiveHookModule (k := k)
          (rankProjectiveHookTagIntoGrid G (Sum.inr a) ht) =
          HookInfinity.module (R := k) b := by
        change HookInfinity.module (R := k) b = HookInfinity.module (R := k) b
        rfl
      have hTgt : HookInfinity.module (R := k) (G.embedding b) =
          rankProjectiveHookModule (k := k) (Sum.inr a) := by
        simp [rankProjectiveHookModule, hbEmb]
      exact (G.lan.mapIso (eqToIso hSrc)).trans
        ((G.infinityLanIso (k := k) b).trans (eqToIso hTgt))

private noncomputable def hookSumGridTag {ι : Type} [Fintype ι]
    (T : ι → RankProjectiveHookTag (Fin n → ℝ)) (j : ι) :
    RankProjectiveHookTag (hookSumCoordinateGrid T).Point :=
  rankProjectiveHookTagIntoGrid (hookSumCoordinateGrid T) (T j)
    (hookSumTag_mem_grid T j)

private noncomputable def hookSumGridTagLanIso {ι : Type} [Fintype ι]
    (T : ι → RankProjectiveHookTag (Fin n → ℝ)) (j : ι) :
    (hookSumCoordinateGrid T).lan.obj
        (rankProjectiveHookModule (k := k) (hookSumGridTag T j)) ≅
      rankProjectiveHookModule (k := k) (T j) := by
  simpa [hookSumGridTag] using
    rankProjectiveHookTagIntoGridLanIso (hookSumCoordinateGrid T) (T j)
      (hookSumTag_mem_grid T j)

/-- Isomorphic finite sums of real-coordinate finite-death and infinite-death
hooks have the same multiplicity for every tag. The endpoint grid is built
from both occurrence families and the queried tag, so no endpoint-membership
hypothesis or decomposition of an ambient module is required. -/
theorem rankProjectiveHookSum_multiplicity_unique_of_iso
    {m r : ℕ} (F : Fin m → RankProjectiveHookTag (Fin n → ℝ))
    (H : Fin r → RankProjectiveHookTag (Fin n → ℝ))
    (e : Nonempty
      ((⨁ fun i => rankProjectiveHookModule (k := k) (F i)) ≅
        ⨁ fun j => rankProjectiveHookModule (k := k) (H j)))
    (c : RankProjectiveHookTag (Fin n → ℝ)) :
    Fintype.card {i : Fin m // F i = c} =
      Fintype.card {j : Fin r // H j = c} := by
  classical
  let T : Fin m ⊕ (Fin r ⊕ Unit) → RankProjectiveHookTag (Fin n → ℝ) :=
    Sum.elim F (Sum.elim H (fun _ => c))
  let G := hookSumCoordinateGrid T
  let F' : Fin m → RankProjectiveHookTag G.Point := fun i => hookSumGridTag T (.inl i)
  let H' : Fin r → RankProjectiveHookTag G.Point := fun j =>
    hookSumGridTag T (.inr (.inl j))
  let c' : RankProjectiveHookTag G.Point := hookSumGridTag T (.inr (.inr ()))
  rcases e with ⟨e⟩
  let eF : G.lan.obj (⨁ fun i => rankProjectiveHookModule (k := k) (F' i)) ≅
      ⨁ fun i => rankProjectiveHookModule (k := k) (F i) :=
    (G.lanBiproductIso (fun i => rankProjectiveHookModule (k := k) (F' i))).trans
      (biproduct.mapIso (fun i => hookSumGridTagLanIso T (.inl i)))
  let eH : G.lan.obj (⨁ fun j => rankProjectiveHookModule (k := k) (H' j)) ≅
      ⨁ fun j => rankProjectiveHookModule (k := k) (H j) :=
    (G.lanBiproductIso (fun j => rankProjectiveHookModule (k := k) (H' j))).trans
      (biproduct.mapIso (fun j => hookSumGridTagLanIso T (.inr (.inl j))))
  let eGrid := eF.trans (e.trans eH.symm)
  let eGridHom := G.lanMapPreimage eGrid.hom
  let eGridInv := G.lanMapPreimage eGrid.inv
  have hmapHom : G.lan.map eGridHom = eGrid.hom := G.lan_map_preimage eGrid.hom
  have hmapInv : G.lan.map eGridInv = eGrid.inv := G.lan_map_preimage eGrid.inv
  have hleft : eGridHom ≫ eGridInv = 𝟙 _ := by
    apply G.lan_map_injective
    calc
      G.lan.map (eGridHom ≫ eGridInv) = G.lan.map eGridHom ≫ G.lan.map eGridInv :=
        Functor.map_comp _ _ _
      _ = eGrid.hom ≫ eGrid.inv := by rw [hmapHom, hmapInv]
      _ = 𝟙 _ := eGrid.hom_inv_id
      _ = G.lan.map (𝟙 _) := by simp
  have hright : eGridInv ≫ eGridHom = 𝟙 _ := by
    apply G.lan_map_injective
    calc
      G.lan.map (eGridInv ≫ eGridHom) = G.lan.map eGridInv ≫ G.lan.map eGridHom :=
        Functor.map_comp _ _ _
      _ = eGrid.inv ≫ eGrid.hom := by rw [hmapHom, hmapInv]
      _ = 𝟙 _ := eGrid.inv_hom_id
      _ = G.lan.map (𝟙 _) := by simp
  let eFinite :
      (⨁ fun i => rankProjectiveHookModule (k := k) (F' i)) ≅
        ⨁ fun j => rankProjectiveHookModule (k := k) (H' j) :=
    ⟨eGridHom, eGridInv, hleft, hright⟩
  have hfinite :=
    FiniteRankProjectiveClassification.rankProjectiveHookSum_multiplicity_unique
      F' H' ⟨eFinite⟩ c'
  have hFiff (i : Fin m) : F i = c ↔ F' i = c' := by
    exact (rankProjectiveHookTagIntoGrid_eq_iff G
      (hookSumTag_mem_grid T (.inl i)) (hookSumTag_mem_grid T (.inr (.inr ())))).symm
  have hHiff (j : Fin r) : H j = c ↔ H' j = c' := by
    exact (rankProjectiveHookTagIntoGrid_eq_iff G
      (hookSumTag_mem_grid T (.inr (.inl j))) (hookSumTag_mem_grid T (.inr (.inr ())))).symm
  let eFCard : {i : Fin m // F i = c} ≃ {i : Fin m // F' i = c'} := {
    toFun := fun i => ⟨i.1, (hFiff i.1).mp i.2⟩
    invFun := fun i => ⟨i.1, (hFiff i.1).mpr i.2⟩
    left_inv := by intro i; cases i; rfl
    right_inv := by intro i; cases i; rfl
  }
  let eHCard : {j : Fin r // H j = c} ≃ {j : Fin r // H' j = c'} := {
    toFun := fun j => ⟨j.1, (hHiff j.1).mp j.2⟩
    invFun := fun j => ⟨j.1, (hHiff j.1).mpr j.2⟩
    left_inv := by intro j; cases j; rfl
    right_inv := by intro j; cases j; rfl
  }
  calc
    Fintype.card {i : Fin m // F i = c} =
        Fintype.card {i : Fin m // F' i = c'} := Fintype.card_congr eFCard
    _ = Fintype.card {j : Fin r // H' j = c'} := hfinite
    _ = Fintype.card {j : Fin r // H j = c} := (Fintype.card_congr eHCard).symm

/-- A finitely presented rank-projective module on real coordinate space is a
finite direct sum of finite-death hooks and principal-upset hooks. The `Fin m`
family records every occurrence, including repeated isomorphism classes. -/
theorem finitelyPresented_rankProjective_iff_exists_hook_sum
    {M : PModule.{u,0,u} k (Fin n → ℝ)}
    (hn : 0 < n)
    (hM : FinitelyPresented (R := k) (P := Fin n → ℝ) M) :
    IsRankProjective M ↔
      ∃ m : ℕ, ∃ t : Fin m → RankProjectiveHookTag (Fin n → ℝ),
        Nonempty (M ≅ ⨁ fun i => rankProjectiveHookModule (k := k) (t i)) := by
  classical
  let _ := hn
  constructor
  · intro hR
    obtain ⟨G, A, hA, e, hcover, _, _⟩ :=
      finitelyPresented_exists_finiteHookRankExactCover hM
    let C : PModule.{u,0,u} k G.Point := FiniteHookDeflation.module A
    let Q : PModule.{u,0,u} k (Fin n → ℝ) := ⨁ fun t => G.embeddedCoverFamily A t
    let c : G.lan.obj C ≅ Q := G.finiteHookDeflationLanIso A
    let f : G.lan.obj C ⟶ G.lan.obj A := G.lan.map (FiniteHookDeflation.π A)
    let π : Q ⟶ M := c.inv ≫ f ≫ e.hom
    let ι : G.lan.obj (kernel (FiniteHookDeflation.π A)) ⟶ Q :=
      G.lan.map (kernel.ι (FiniteHookDeflation.π A)) ≫ c.hom
    have hπ : IsRankExact ι π := by
      simpa [ι, π, c, f, Category.assoc] using hcover
    obtain ⟨β, hβ⟩ := hR _ _ _ ι π hπ (𝟙 M)
    let t : G.lan.obj A ⟶ G.lan.obj C := e.hom ≫ β ≫ c.inv
    have ht : t ≫ f = 𝟙 (G.lan.obj A) := by
      apply (cancel_mono e.hom).mp
      have hβ' : β ≫ c.inv ≫ f ≫ e.hom = 𝟙 M := by
        simpa [π, f, Category.assoc] using hβ
      change (t ≫ f) ≫ e.hom = e.hom
      calc
        (t ≫ f) ≫ e.hom = e.hom ≫ (β ≫ c.inv ≫ f ≫ e.hom) := by
          simp [t, Category.assoc]
        _ = e.hom := by rw [hβ']; simp
    let s : A ⟶ C := G.lanMapPreimage t
    have hmap : G.lan.map s = t := G.lan_map_preimage t
    have hs : s ≫ FiniteHookDeflation.π A = 𝟙 A := by
      apply G.lan_map_injective
      calc
        G.lan.map (s ≫ FiniteHookDeflation.π A) =
            G.lan.map s ≫ G.lan.map (FiniteHookDeflation.π A) :=
          Functor.map_comp _ _ _
        _ = t ≫ f := by
          simpa [f] using congrArg
            (fun g => g ≫ G.lan.map (FiniteHookDeflation.π A)) hmap
        _ = 𝟙 (G.lan.obj A) := ht
        _ = G.lan.map (𝟙 A) := by simp
    have hAproj : IsRankProjective A :=
      (FiniteHookDeflation.isRankProjective A).of_retract s
        (FiniteHookDeflation.π A) hs
    obtain ⟨S, ⟨eA⟩⟩ :=
      (FiniteRankProjectiveClassification.rankProjective_iff_exists_canonical_subfamily
        A hA).mp hAproj
    let tagsS : S → RankProjectiveHookTag (Fin n → ℝ) :=
      fun i => embeddedCoverTag G A i.1
    let v : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
    let tags : Fin (Fintype.card S) → RankProjectiveHookTag (Fin n → ℝ) :=
      fun i => tagsS (v i)
    let summands : Fin (Fintype.card S) → PModule.{u,0,u} k (Fin n → ℝ) :=
      fun i => rankProjectiveHookModule (k := k) (tags i)
    let eLanA := G.lan.mapIso eA
    let eBip := G.lanBiproductIso (fun i : S => FiniteHookDeflation.family A i.1)
    let eHooks := biproduct.mapIso (fun i : S =>
      embeddedCoverOccurrenceLanIso G A i.1)
    have hfamily :
        summands ∘ v.symm =
          (fun i : S => rankProjectiveHookModule (k := k) (tagsS i)) := by
      funext i
      simp [summands, tags, tagsS]
    have eReindex :
        (⨁ fun i : S => rankProjectiveHookModule (k := k) (tagsS i)) ≅ ⨁ summands := by
      simpa only [hfamily] using (biproduct.reindex v.symm summands)
    refine ⟨Fintype.card S, tags, ?_⟩
    exact ⟨e.symm.trans (eLanA.trans (eBip.trans (eHooks.trans eReindex)))⟩
  · rintro ⟨m, t, ⟨e⟩⟩
    have hsum : IsRankProjective
        (⨁ fun i : Fin m => rankProjectiveHookModule (k := k) (t i)) :=
      IsRankProjective.biproduct _ (fun i => by
        cases t i with
        | inl ab => exact Hook.isRankProjective ab.property
        | inr a => exact HookInfinity.isRankProjective a)
    exact hsum.of_iso e.symm

end TDA.Persistence.GradedFree
