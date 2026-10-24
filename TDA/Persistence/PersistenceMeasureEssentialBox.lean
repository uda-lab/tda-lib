import TDA.Persistence.PersistenceMeasureBox
import TDA.Persistence.PersistenceMeasureEssential

/-!
# Interleaving bounds on the essential boundary

An interleaving transports finite-target image quotients between expanded birth
strips and compares their defined natural-number minima. For q-tame modules on
both sides these minima are the genuine death-at-infinity boundary measures.
In that setting this is the positive-death boundary case of CDSGO,
*The structure and stability of persistence modules*, arXiv:1207.3674v3,
Proposition 4.23, with the boundary measure defined as in §2.6.
-/

universe u w

namespace TDA.Persistence.RealInterleaving

open CategoryTheory
open scoped NNReal

variable {k : Type u} [Field k] {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}

private theorem tail_box_shifted (i : RealInterleaving ε M N)
    {A b C : ℝ} (hab : A + (ε : ℝ) ≤ b) (hbc : b + (ε : ℝ) ≤ C)
    [FiniteDimensional k (persistenceImage N hbc)] :
    persistenceTailMeasureValue M hab
        (show b ≤ C + (ε : ℝ) by have := ε.coe_nonneg; linarith) ≤
      persistenceTailMeasureValue N
        (show A ≤ b + (ε : ℝ) by have := ε.coe_nonneg; linarith) hbc := by
  have hab' : A ≤ b + (ε : ℝ) := by have := ε.coe_nonneg; linarith
  have hbc' : b ≤ C + (ε : ℝ) := by have := ε.coe_nonneg; linarith
  let U := persistenceImage N hbc
  let E := persistenceImage N (hab'.trans hbc)
  let V := persistenceImage M hbc'
  let F := persistenceImage M (hab.trans hbc')
  let L : Submodule k U := V.comap ((i.ψ.app C).hom.comp U.subtype)
  let g : L →ₗ[k] V :=
    ((i.ψ.app C).hom.comp (U.subtype.comp L.subtype)).codRestrict V
      (fun x => x.property)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    let z := structureMapLinear N hbc ((i.φ.app b).hom x)
    have hz : (i.ψ.app C).hom z = y.val := by
      have h := LinearMap.congr_fun (i.crossing_factorization hbc) x
      exact h.trans hx
    refine ⟨⟨⟨z, ⟨(i.φ.app b).hom x, rfl⟩⟩, ?_⟩, ?_⟩
    · change (i.ψ.app C).hom z ∈ V
      rw [hz]
      exact y.property
    · exact Subtype.ext hz
  let Q := (E.comap U.subtype).comap L.subtype
  let q := (F.comap V.subtype).mkQ
  have hQ : Q ≤ LinearMap.ker (q.comp g) := by
    intro z hz
    change q (g z) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨x, hx⟩ := hz
    refine ⟨(i.ψ.app A).hom x, ?_⟩
    have hn := congrArg ModuleCat.Hom.hom
      (i.ψ.naturality (homOfLE (hab'.trans hbc)))
    have hn' := LinearMap.congr_fun hn x
    change (i.ψ.app C).hom (structureMapLinear N (hab'.trans hbc) x) =
      structureMapLinear M (hab.trans hbc') ((i.ψ.app A).hom x) at hn'
    rw [hx] at hn'
    exact hn'.symm
  let f : L ⧸ Q →ₗ[k] V ⧸ F.comap V.subtype := Q.liftQ (q.comp g) hQ
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨z, hz⟩ := (F.comap V.subtype).mkQ_surjective y
    obtain ⟨x, hx⟩ := hg z
    exact ⟨Q.mkQ x, by change q (g x) = y; rw [hx]; exact hz⟩
  let j : L ⧸ Q →ₗ[k] U ⧸ E.comap U.subtype :=
    Q.mapQ (E.comap U.subtype) L.subtype le_rfl
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero (E.comap U.subtype)).mp hx)
  exact (LinearMap.finrank_le_finrank_of_surjective hf).trans
    (LinearMap.finrank_le_finrank_of_injective hj)

/-- Finite-target birth strips obey the box inequality when the expanded crossing
image is finite-dimensional. No finiteness assumption on either fiber is needed. -/
theorem persistenceTailMeasureValue_box_le (i : RealInterleaving ε M N)
    {a b c : ℝ} (hab : a ≤ b) (hgap : b + (ε : ℝ) ≤ c - (ε : ℝ))
    [FiniteDimensional k (persistenceImage N hgap)] :
    persistenceTailMeasureValue M hab
        (show b ≤ c by have := ε.coe_nonneg; linarith) ≤
      persistenceTailMeasureValue N
        (show a - (ε : ℝ) ≤ b + (ε : ℝ) by have := ε.coe_nonneg; linarith) hgap := by
  have h := i.tail_box_shifted
    (show (a - (ε : ℝ)) + (ε : ℝ) ≤ b by simpa using hab) hgap
  simpa only [sub_add_cancel] using h

/-- The defined natural-valued `Module.finrank` minima obey a box inequality under an actual interleaving.
Only target q-tameness is needed for this inequality. Interpreting the source minimum
as its eventual essential boundary count additionally requires source q-tameness. -/
theorem essentialMeasureValue_box_le_of_qTame (i : RealInterleaving ε M N)
    (hN : N.QTame) {a b : ℝ} (hab : a ≤ b) :
    essentialMeasureValue M hab ≤ essentialMeasureValue N
      (show a - (ε : ℝ) ≤ b + (ε : ℝ) by have := ε.coe_nonneg; linarith) := by
  have hab' : a - (ε : ℝ) ≤ b + (ε : ℝ) := by have := ε.coe_nonneg; linarith
  obtain ⟨C, hC, hE⟩ := exists_tail_eq_essentialMeasureValue N hab'
  have : FiniteDimensional k (persistenceImage N hC.le) := hN _ _ hC
  have hbC : b < C + (ε : ℝ) := by have := ε.coe_nonneg; linarith
  have h := i.tail_box_shifted
    (show (a - (ε : ℝ)) + (ε : ℝ) ≤ b by simpa using hab) hC.le
  have h' : persistenceTailMeasureValue M hab hbC.le ≤
      persistenceTailMeasureValue N hab' hC.le := by
    simpa only [sub_add_cancel] using h
  exact (essentialMeasureValue_le_tail M hab hbC).trans (h'.trans_eq hE)

end TDA.Persistence.RealInterleaving
