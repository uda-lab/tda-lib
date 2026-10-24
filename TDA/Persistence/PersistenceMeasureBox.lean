import TDA.Persistence.PersistenceMeasure

/-!
# Box inequalities for persistence measures

An interleaving compares the image quotients of a rectangle and its thickening.
The linear algebra uses only finite-dimensionality of the expanded crossing image.
This is the box lemma of Chazal–de Silva–Glisse–Oudot,
*The structure and stability of persistence modules*, arXiv:1207.3674v3, Lemma 4.22.
-/

universe u w

namespace TDA.Persistence

open CategoryTheory
open scoped NNReal

variable {k : Type u} [Field k]

private theorem quotient_finrank_le_of_surjective_subspace
    {X Y : Type w} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [FiniteDimensional k X] (E L : Submodule k X) (f : L →ₗ[k] Y)
    (hf : Function.Surjective f) (hE : E.comap L.subtype ≤ LinearMap.ker f) :
    Module.finrank k Y ≤ Module.finrank k (X ⧸ E) := by
  let Q := E.comap L.subtype
  let g : L ⧸ Q →ₗ[k] Y := Q.liftQ f hE
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨Q.mkQ x, hx⟩
  let j : L ⧸ Q →ₗ[k] X ⧸ E := Q.mapQ E L.subtype le_rfl
  have hj : Function.Injective j := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero E).mp hx)
  exact (LinearMap.finrank_le_finrank_of_surjective hg).trans
    (LinearMap.finrank_le_finrank_of_injective hj)

private theorem quotient_finrank_le_of_image
    {X Y : Type w} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (U E : Submodule k X) (V F : Submodule k Y) (f : X →ₗ[k] Y)
    [FiniteDimensional k U]
    (hV : V ≤ U.map f) (hE : E ⊓ V.comap f ≤ F.comap f) :
    Module.finrank k (V ⧸ F.comap V.subtype) ≤
      Module.finrank k (U ⧸ E.comap U.subtype) := by
  let L : Submodule k U := V.comap (f.comp U.subtype)
  let g : L →ₗ[k] V :=
    (f.comp (U.subtype.comp L.subtype)).codRestrict V (fun x => x.property)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hV y.property
    refine ⟨⟨⟨x, hx⟩, ?_⟩, ?_⟩
    · change f x ∈ V
      simpa only [hxy] using y.property
    · exact Subtype.ext hxy
  let q := (F.comap V.subtype).mkQ
  apply quotient_finrank_le_of_surjective_subspace (E.comap U.subtype) L (q.comp g)
    ((F.comap V.subtype).mkQ_surjective.comp hg)
  intro x hx
  change q (g x) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact hE ⟨hx, x.property⟩

namespace RealInterleaving

variable {ε : ℝ≥0} {M N : PModule.{u,0,w} k ℝ}

private theorem shifted_naturality (f : M ⟶ (RealShift.shift ε).obj N)
    {s t : ℝ} (h : s ≤ t) :
    (f.app t).hom.comp (structureMapLinear M h) =
      (structureMapLinear N (add_le_add h (le_refl (ε : ℝ)))).comp (f.app s).hom := by
  exact congrArg ModuleCat.Hom.hom (f.naturality (homOfLE h))

/-- A crossing structure map factors through the crossing image of the other module. -/
theorem crossing_factorization (i : RealInterleaving ε M N) {b C : ℝ}
    (h : b + (ε : ℝ) ≤ C) :
    (i.ψ.app C).hom.comp
        ((structureMapLinear N h).comp (i.φ.app b).hom) =
      structureMapLinear M (show b ≤ C + (ε : ℝ) by
        have := ε.coe_nonneg; linarith) := by
  erw [← LinearMap.comp_assoc, shifted_naturality i.ψ h,
    LinearMap.comp_assoc]
  have hi := congrArg ModuleCat.Hom.hom (i.φ_ψ_structureMap b)
  change (i.ψ.app (b + (ε : ℝ))).hom.comp (i.φ.app b).hom = _ at hi
  erw [hi, ← structureMapLinear_comp]

private theorem crossing_to_shift (i : RealInterleaving ε M N) {C d : ℝ}
    (h : C + (ε : ℝ) ≤ d) :
    (i.φ.app d).hom.comp
        ((structureMapLinear M h).comp (i.ψ.app C).hom) =
      structureMapLinear N (show C ≤ d + (ε : ℝ) by
        have := ε.coe_nonneg; linarith) := by
  erw [← LinearMap.comp_assoc, shifted_naturality i.φ h,
    LinearMap.comp_assoc]
  have hi := congrArg ModuleCat.Hom.hom (i.symm.φ_ψ_structureMap C)
  change (i.φ.app (C + (ε : ℝ))).hom.comp (i.ψ.app C).hom = _ at hi
  erw [hi, ← structureMapLinear_comp]

private theorem measure_box_shifted (i : RealInterleaving ε M N)
    {A b C d : ℝ} (hab : A + (ε : ℝ) ≤ b) (hbc : b + (ε : ℝ) ≤ C)
    (hcd : C + (ε : ℝ) ≤ d)
    [FiniteDimensional k (persistenceImage N hbc)] :
    persistenceMeasureValue M hab
        (show b ≤ C + (ε : ℝ) by have := ε.coe_nonneg; linarith) hcd ≤
      persistenceMeasureValue N
        (show A ≤ b + (ε : ℝ) by have := ε.coe_nonneg; linarith) hbc
        (show C ≤ d + (ε : ℝ) by have := ε.coe_nonneg; linarith) := by
  have hab' : A ≤ b + (ε : ℝ) := by have := ε.coe_nonneg; linarith
  have hbc' : b ≤ C + (ε : ℝ) := by have := ε.coe_nonneg; linarith
  have hcd' : C ≤ d + (ε : ℝ) := by have := ε.coe_nonneg; linarith
  have hAC : A ≤ C := hab'.trans hbc
  have : FiniteDimensional k (persistenceKernel N hbc hcd') :=
    Submodule.finiteDimensional_of_le inf_le_left
  apply quotient_finrank_le_of_image
    (persistenceKernel N hbc hcd') (persistenceKernel N hAC hcd')
    (persistenceKernel M hbc' hcd) (persistenceKernel M (hab.trans hbc') hcd)
    (i.ψ.app C).hom
  · intro y hy
    obtain ⟨x, hx⟩ := hy.1
    let z := structureMapLinear N hbc ((i.φ.app b).hom x)
    have hz : (i.ψ.app C).hom z = y := by
      have hi := LinearMap.congr_fun (i.crossing_factorization hbc) x
      exact hi.trans hx
    refine ⟨z, ⟨⟨(i.φ.app b).hom x, rfl⟩, ?_⟩, hz⟩
    change structureMapLinear N hcd' z = 0
    have hd := LinearMap.congr_fun (i.crossing_to_shift hcd) z
    change (i.φ.app d).hom (structureMapLinear M hcd ((i.ψ.app C).hom z)) = _ at hd
    rw [hz, show structureMapLinear M hcd y = 0 from hy.2, map_zero] at hd
    exact hd.symm
  · intro z hz
    obtain ⟨x, hx⟩ := hz.1.1
    refine ⟨?_, hz.2.2⟩
    refine ⟨(i.ψ.app A).hom x, ?_⟩
    have hi := LinearMap.congr_fun (shifted_naturality i.ψ hAC) x
    change (i.ψ.app C).hom (structureMapLinear N hAC x) = _ at hi
    rw [hx] at hi
    exact hi.symm

/-- The box inequality needs only a finite crossing image in the expanded rectangle.
The original module may have infinite-dimensional fibers and need not be q-tame. -/
theorem persistenceMeasureValue_box_le (i : RealInterleaving ε M N)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hgap : b + (ε : ℝ) ≤ c - (ε : ℝ))
    [FiniteDimensional k (persistenceImage N hgap)] :
    persistenceMeasureValue M hab
        (show b ≤ c by have := ε.coe_nonneg; linarith) hcd ≤
      persistenceMeasureValue N
        (show a - (ε : ℝ) ≤ b + (ε : ℝ) by have := ε.coe_nonneg; linarith)
        hgap (show c - (ε : ℝ) ≤ d + (ε : ℝ) by have := ε.coe_nonneg; linarith) := by
  have h := i.measure_box_shifted
    (show (a - (ε : ℝ)) + (ε : ℝ) ≤ b by simpa using hab) hgap
    (show (c - (ε : ℝ)) + (ε : ℝ) ≤ d by simpa using hcd)
  simpa only [sub_add_cancel] using h

/-- Q-tameness gives the box inequality whenever the thickened rectangle is strictly
above the diagonal. This is the finite-rectangle part of CDSGO Lemma 4.22. -/
theorem persistenceMeasureValue_box_le_of_qTame (i : RealInterleaving ε M N)
    (hN : N.QTame) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hgap : 2 * (ε : ℝ) < c - b) :
    persistenceMeasureValue M hab
        (show b ≤ c by have := ε.coe_nonneg; linarith) hcd ≤
      persistenceMeasureValue N
        (show a - (ε : ℝ) ≤ b + (ε : ℝ) by have := ε.coe_nonneg; linarith)
        (show b + (ε : ℝ) ≤ c - (ε : ℝ) by linarith)
        (show c - (ε : ℝ) ≤ d + (ε : ℝ) by have := ε.coe_nonneg; linarith) := by
  have hcross : b + (ε : ℝ) < c - (ε : ℝ) := by linarith
  have : FiniteDimensional k (persistenceImage N hcross.le) := hN _ _ hcross
  exact i.persistenceMeasureValue_box_le hab hcd hcross.le

end RealInterleaving
end TDA.Persistence
