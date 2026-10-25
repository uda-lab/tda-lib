import TDA.Persistence.FinitePresentationHookCover
import TDA.Persistence.FiniteRankProjectiveClassification

/-!
# Rank-projectives among finitely presented real-coordinate modules

For a finitely presented module on real coordinate space, the actual finite-grid
hook cover splits when the module is rank projective. Full faithfulness of the
grid left Kan extension descends that splitting to the finite grid, where the
finite-poset classification applies. The resulting selected hook occurrences
are transported back through the actual Lan and finite-biproduct comparisons.
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
