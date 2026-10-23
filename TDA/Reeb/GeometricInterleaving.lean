import TDA.Reeb.QuotientThickeningAbsorption

/-!
# Geometric interleavings of graph objects

Write `U_ε = geometricSmoothing ε` on graph objects, `ζ^ε : 𝟭 ⟶ U_ε` for the geometric unit,
`μ_(ε,δ) : U_ε U_δ ≅ U_(ε+δ)` for the semigroup isomorphism `geometricSmoothingCompIso`,
`C = cosheafFunctor` and `β^ε : U_ε ⋙ C ≅ C ⋙ constructibleSmoothing ε` for the comparison.

A **geometric `ε`-interleaving** of graph objects `A`, `B` (the statement shape of DMP
Definition 4.36, proved here independently) is a pair `φ : A ⟶ U_ε B`, `ψ : B ⟶ U_ε A` whose
shifted composites `A ⟶ U_ε B ⟶ U_ε U_ε A ≅ U_(ε+ε) A` and its mirror are the units
`ζ^(ε+ε)`. The parameter is the literal `ε + ε`, as in the precosheaf `Interleaving`.
`0`-interleavings are exactly isomorphisms (`GeometricInterleaving.nonempty_zero_iff`).

The **geometric interleaving distance** `geometricInterleavingDistance A B : ℝ≥0∞` is the
infimum of the parameters carrying an interleaving (the shape of DMP Definition 4.4). It is a
plain function; no `EDist` instance is installed.

The **transport** `cosheafShiftMap φ = C φ ≫ β^ε` sends geometric shifted maps to shifted maps of
the underlying precosheaves. It respects units (`cosheafShiftMap_unit`, from the merged unit
compatibility) and shifted composites (`cosheafShiftMap_comp`, from naturality of `β` and the
merged compatibility of `μ` with `smoothingCompIso`). So every geometric interleaving gives a
precosheaf interleaving of the component cosheaves (`GeometricInterleaving.toCosheaf`), and the
cosheaf interleaving distance is at most the geometric one
(`interleavingDistance_cosheafFunctor_le_geometricInterleavingDistance`). Neither full
faithfulness of `C` nor the cosheaf equivalence is used.

Everything is in universe `0`, the universe of `RGraphCat`.

See `docs/math/reeb-geometric-interleaving.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal ENNReal

namespace TDA.Reeb

noncomputable section

namespace RGraph

open OpenInterval

local notation "ℛ" => ReebQuotient.quotientFunctor ℝ

/-! ### Unit coherence -/

/-- **Unit coherence, first form**: `A ⟶ U_δ A ⟶ U_ε U_δ A ≅ U_(ε+δ) A` is `ζ^(ε+δ)`. -/
theorem geometricSmoothingUnit_comp_geometricSmoothingUnit (ε δ : ℝ≥0) (A : RGraphCat) :
    (geometricSmoothingUnit δ).app A ≫
        (geometricSmoothingUnit ε).app ((geometricSmoothing δ).obj A) ≫
          (geometricSmoothingCompIso ε δ).hom.app A =
      (geometricSmoothingUnit (ε + δ)).app A := by
  ext x
  exact (geometricSmoothingCompIso_hom_app_hom_left_mk ε δ A
      (GeometricThickening.zeroSection A.obj.left δ x)
      ⟨0, GeometricThickening.zero_mem_band ε⟩).trans
    (congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext (add_zero (0 : ℝ)))))

/-- **Unit coherence, second form**: `A ⟶ U_ε A ⟶ U_ε U_δ A ≅ U_(ε+δ) A` is `ζ^(ε+δ)`. -/
theorem geometricSmoothingUnit_comp_map_geometricSmoothingUnit (ε δ : ℝ≥0) (A : RGraphCat) :
    (geometricSmoothingUnit ε).app A ≫
        (geometricSmoothing ε).map ((geometricSmoothingUnit δ).app A) ≫
          (geometricSmoothingCompIso ε δ).hom.app A =
      (geometricSmoothingUnit (ε + δ)).app A := by
  ext x
  exact (geometricSmoothingCompIso_hom_app_hom_left_mk ε δ A
      (GeometricThickening.zeroSection A.obj.left δ x)
      ⟨0, GeometricThickening.zero_mem_band ε⟩).trans
    (congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext (add_zero (0 : ℝ)))))

/-- **Parameter equalities fix the unit**: `ζ^ε` followed by the band-inclusion isomorphism
`U_ε ≅ U_δ` of `ε = δ` is `ζ^δ`. -/
theorem geometricSmoothingUnit_comp_geometricSmoothingEqIso {ε δ : ℝ≥0} (h : ε = δ) :
    geometricSmoothingUnit ε ≫ (geometricSmoothingEqIso h).hom = geometricSmoothingUnit δ := by
  ext A x
  rfl

/-! ### Thin targets -/

/-- Two graph maps into a target whose height fibres are subsingletons are equal: both send `x`
into the fibre over the height of `x`. -/
theorem hom_ext_of_fiber_subsingleton {X Y : RGraphCat} {f g : X ⟶ Y}
    (hY : ∀ t : ℝ, Subsingleton (overBaseMap Y.obj ⁻¹' {t})) : f = g := by
  ext x
  have h₁ : f.hom.left.hom x ∈ overBaseMap Y.obj ⁻¹' {overBaseMap X.obj x} :=
    overBaseMap_comm f.hom x
  have h₂ : g.hom.left.hom x ∈ overBaseMap Y.obj ⁻¹' {overBaseMap X.obj x} :=
    overBaseMap_comm g.hom x
  exact congrArg Subtype.val ((hY _).elim ⟨_, h₁⟩ ⟨_, h₂⟩)

/-! ### Geometric interleavings -/

/-- A **geometric `ε`-interleaving** of graph objects (DMP Definition 4.36, statement shape;
proved here independently): `φ : A ⟶ U_ε B` and `ψ : B ⟶ U_ε A` whose shifted composites
`A ⟶ U_ε B ⟶ U_ε U_ε A ≅ U_(ε+ε) A` and `B ⟶ U_ε A ⟶ U_ε U_ε B ≅ U_(ε+ε) B` are the
`ε + ε` units. -/
structure GeometricInterleaving (ε : ℝ≥0) (A B : RGraphCat) where
  /-- `A ⟶ U_ε B`. -/
  φ : A ⟶ (geometricSmoothing ε).obj B
  /-- `B ⟶ U_ε A`. -/
  ψ : B ⟶ (geometricSmoothing ε).obj A
  φ_ψ : φ ≫ (geometricSmoothing ε).map ψ ≫ (geometricSmoothingCompIso ε ε).hom.app A =
    (geometricSmoothingUnit (ε + ε)).app A
  ψ_φ : ψ ≫ (geometricSmoothing ε).map φ ≫ (geometricSmoothingCompIso ε ε).hom.app B =
    (geometricSmoothingUnit (ε + ε)).app B

namespace GeometricInterleaving

variable {ε : ℝ≥0} {A B : RGraphCat}

@[ext] theorem ext {i j : GeometricInterleaving ε A B} (hφ : i.φ = j.φ) (hψ : i.ψ = j.ψ) :
    i = j := by
  cases i; cases j; cases hφ; cases hψ; rfl

/-- Symmetry: swap the two maps. -/
def symm (i : GeometricInterleaving ε A B) : GeometricInterleaving ε B A where
  φ := i.ψ
  ψ := i.φ
  φ_ψ := i.ψ_φ
  ψ_φ := i.φ_ψ

/-- The unit interleaving of `A` with itself: both maps are `ζ^ε`. -/
def refl (ε : ℝ≥0) (A : RGraphCat) : GeometricInterleaving ε A A where
  φ := (geometricSmoothingUnit ε).app A
  ψ := (geometricSmoothingUnit ε).app A
  φ_ψ := geometricSmoothingUnit_comp_map_geometricSmoothingUnit ε ε A
  ψ_φ := geometricSmoothingUnit_comp_map_geometricSmoothingUnit ε ε A

/-- The shifted composite of `e ≫ ζ^0` and `e' ≫ ζ^0` for an inverse pair is the unit. -/
private theorem ofIso_triangle {A B : RGraphCat} (f : A ⟶ B) (g : B ⟶ A) (hfg : f ≫ g = 𝟙 A) :
    (f ≫ (geometricSmoothingUnit 0).app B) ≫
        (geometricSmoothing 0).map (g ≫ (geometricSmoothingUnit 0).app A) ≫
          (geometricSmoothingCompIso 0 0).hom.app A =
      (geometricSmoothingUnit (0 + 0)).app A := by
  have hn : (geometricSmoothingUnit 0).app B ≫ (geometricSmoothing 0).map g =
      g ≫ (geometricSmoothingUnit 0).app A :=
    ((geometricSmoothingUnit 0).naturality g).symm
  calc (f ≫ (geometricSmoothingUnit 0).app B) ≫
          (geometricSmoothing 0).map (g ≫ (geometricSmoothingUnit 0).app A) ≫
            (geometricSmoothingCompIso 0 0).hom.app A
      = f ≫ ((geometricSmoothingUnit 0).app B ≫ (geometricSmoothing 0).map g) ≫
          (geometricSmoothing 0).map ((geometricSmoothingUnit 0).app A) ≫
            (geometricSmoothingCompIso 0 0).hom.app A := by
        rw [Functor.map_comp]; simp only [Category.assoc]
    _ = (f ≫ g) ≫ (geometricSmoothingUnit 0).app A ≫
          (geometricSmoothing 0).map ((geometricSmoothingUnit 0).app A) ≫
            (geometricSmoothingCompIso 0 0).hom.app A := by
        rw [hn]; simp only [Category.assoc]
    _ = (geometricSmoothingUnit (0 + 0)).app A := by
        rw [hfg, Category.id_comp]
        exact geometricSmoothingUnit_comp_map_geometricSmoothingUnit 0 0 A

/-- An isomorphism gives a `0`-interleaving: `φ = e.hom ≫ ζ^0`, `ψ = e.inv ≫ ζ^0`. -/
def ofIso (e : A ≅ B) : GeometricInterleaving 0 A B where
  φ := e.hom ≫ (geometricSmoothingUnit 0).app B
  ψ := e.inv ≫ (geometricSmoothingUnit 0).app A
  φ_ψ := ofIso_triangle e.hom e.inv e.hom_inv_id
  ψ_φ := ofIso_triangle e.inv e.hom e.inv_hom_id

/-- A `0`-triangle, read through `U_0 ≅ 𝟭`, is an inverse law. -/
private theorem toIso_comp {A B : RGraphCat} (φ : A ⟶ (geometricSmoothing 0).obj B)
    (ψ : B ⟶ (geometricSmoothing 0).obj A)
    (h : φ ≫ (geometricSmoothing 0).map ψ ≫ (geometricSmoothingCompIso 0 0).hom.app A =
      (geometricSmoothingUnit (0 + 0)).app A) :
    (φ ≫ geometricSmoothingZeroIso.hom.app B) ≫ ψ ≫ geometricSmoothingZeroIso.hom.app A =
      𝟙 A := by
  have hZ : geometricSmoothingZeroIso.hom.app ((geometricSmoothing 0).obj A) =
      (geometricSmoothingCompIso 0 0).hom.app A ≫
        (geometricSmoothingEqIso (zero_add (0 : ℝ≥0))).hom.app A :=
    ((congrArg (fun e => e.hom.app A) (geometricSmoothingCompIso_zero_left 0)).trans
      (Category.comp_id _)).symm
  have hU : (geometricSmoothingUnit (0 + 0)).app A ≫
      (geometricSmoothingEqIso (zero_add (0 : ℝ≥0))).hom.app A =
        (geometricSmoothingUnit 0).app A :=
    congrArg (fun t => t.app A)
      (geometricSmoothingUnit_comp_geometricSmoothingEqIso (zero_add (0 : ℝ≥0)))
  have hn : geometricSmoothingZeroIso.hom.app B ≫ ψ =
      (geometricSmoothing 0).map ψ ≫ geometricSmoothingZeroIso.hom.app _ :=
    (geometricSmoothingZeroIso.hom.naturality ψ).symm
  calc (φ ≫ geometricSmoothingZeroIso.hom.app B) ≫ ψ ≫ geometricSmoothingZeroIso.hom.app A
      = φ ≫ (geometricSmoothingZeroIso.hom.app B ≫ ψ) ≫ geometricSmoothingZeroIso.hom.app A := by
        simp only [Category.assoc]
    _ = (φ ≫ (geometricSmoothing 0).map ψ ≫ (geometricSmoothingCompIso 0 0).hom.app A) ≫
          (geometricSmoothingEqIso (zero_add (0 : ℝ≥0))).hom.app A ≫
            geometricSmoothingZeroIso.hom.app A := by
        rw [hn, hZ]; simp only [Category.assoc]
    _ = (geometricSmoothingUnit 0).app A ≫ geometricSmoothingZeroIso.hom.app A := by
        rw [h, ← Category.assoc, hU]
    _ = 𝟙 A := by
        rw [geometricSmoothingUnit_zero, Iso.inv_hom_id_app]
        rfl

/-- A `0`-interleaving gives an isomorphism through `U_0 ≅ 𝟭`. -/
def toIso (i : GeometricInterleaving 0 A B) : A ≅ B where
  hom := i.φ ≫ geometricSmoothingZeroIso.hom.app B
  inv := i.ψ ≫ geometricSmoothingZeroIso.hom.app A
  hom_inv_id := toIso_comp i.φ i.ψ i.φ_ψ
  inv_hom_id := toIso_comp i.ψ i.φ i.ψ_φ

/-- `0`-interleavings exist exactly between isomorphic graph objects. -/
theorem nonempty_zero_iff : Nonempty (GeometricInterleaving 0 A B) ↔ Nonempty (A ≅ B) :=
  ⟨fun ⟨i⟩ => ⟨i.toIso⟩, fun ⟨e⟩ => ⟨ofIso e⟩⟩

end GeometricInterleaving

/-! ### The geometric interleaving distance -/

/-- The **geometric interleaving distance** (the shape of DMP Definition 4.4, proved here
independently on graph objects): `⨅ ε ≥ 0 with a geometric ε-interleaving, ε` in `[0, ∞]`. -/
noncomputable def geometricInterleavingDistance (A B : RGraphCat) : ℝ≥0∞ :=
  ⨅ (ε : ℝ≥0) (_ : Nonempty (GeometricInterleaving ε A B)), (ε : ℝ≥0∞)

variable {A B : RGraphCat}

/-- A witness bounds the distance. -/
theorem geometricInterleavingDistance_le_of_nonempty {ε : ℝ≥0}
    (h : Nonempty (GeometricInterleaving ε A B)) : geometricInterleavingDistance A B ≤ ε :=
  iInf₂_le ε h

/-- An explicit geometric `ε`-interleaving gives `d_geo A B ≤ ε`. -/
theorem GeometricInterleaving.geometricInterleavingDistance_le {ε : ℝ≥0}
    (i : GeometricInterleaving ε A B) : geometricInterleavingDistance A B ≤ ε :=
  geometricInterleavingDistance_le_of_nonempty ⟨i⟩

/-- Lower-envelope property of the infimum. -/
theorem le_geometricInterleavingDistance_iff {r : ℝ≥0∞} :
    r ≤ geometricInterleavingDistance A B ↔
      ∀ ε : ℝ≥0, Nonempty (GeometricInterleaving ε A B) → r ≤ ε :=
  le_iInf₂_iff

/-- Empty witness set gives `⊤`, and conversely. -/
theorem geometricInterleavingDistance_eq_top_iff :
    geometricInterleavingDistance A B = ⊤ ↔ ∀ ε : ℝ≥0, IsEmpty (GeometricInterleaving ε A B) := by
  simp only [geometricInterleavingDistance, iInf_eq_top, ENNReal.coe_ne_top, imp_false,
    not_nonempty_iff]

/-- A geometric `0`-interleaving gives distance `0`. -/
theorem GeometricInterleaving.geometricInterleavingDistance_eq_zero
    (i : GeometricInterleaving 0 A B) : geometricInterleavingDistance A B = 0 :=
  nonpos_iff_eq_zero.1 (by simpa using i.geometricInterleavingDistance_le)

theorem geometricInterleavingDistance_self (A : RGraphCat) :
    geometricInterleavingDistance A A = 0 :=
  (GeometricInterleaving.refl 0 A).geometricInterleavingDistance_eq_zero

theorem geometricInterleavingDistance_eq_zero_of_iso (e : A ≅ B) :
    geometricInterleavingDistance A B = 0 :=
  (GeometricInterleaving.ofIso e).geometricInterleavingDistance_eq_zero

theorem geometricInterleavingDistance_comm (A B : RGraphCat) :
    geometricInterleavingDistance A B = geometricInterleavingDistance B A :=
  le_antisymm (le_iInf₂ fun _ ⟨i⟩ => i.symm.geometricInterleavingDistance_le)
    (le_iInf₂ fun _ ⟨i⟩ => i.symm.geometricInterleavingDistance_le)

/-! ### Transport to the cosheaf side -/

/-- The **shifted map** of `φ : A ⟶ U_ε B` on the underlying precosheaves:
`C A ⟶ C (U_ε B) ≅ S_ε C B`, that is `C φ` followed by the comparison `β^ε`. -/
def cosheafShiftMap {ε : ℝ≥0} {A B : RGraphCat} (φ : A ⟶ (geometricSmoothing ε).obj B) :
    (cosheafFunctor.obj A).obj ⟶ (smoothing ε).obj (cosheafFunctor.obj B).obj :=
  (cosheafFunctor.map φ).hom ≫ ((geometricSmoothingComparisonIso ε).hom.app B).hom

/-- The shifted map of the geometric unit is the smoothing unit (merged unit compatibility). -/
theorem cosheafShiftMap_unit (ε : ℝ≥0) (A : RGraphCat) :
    cosheafShiftMap ((geometricSmoothingUnit ε).app A) =
      (smoothingUnit ε).app (cosheafFunctor.obj A).obj :=
  intervalComponentsOver_map_geometricSmoothingUnit_comp ε A

/-- The shifted map of a geometric shifted composite is the precosheaf shifted composite: from
naturality of `β^ε` and the merged compatibility of `μ` with `smoothingCompIso`. -/
theorem cosheafShiftMap_comp {ε δ : ℝ≥0} {A B : RGraphCat}
    (φ : A ⟶ (geometricSmoothing ε).obj B) (ψ : B ⟶ (geometricSmoothing δ).obj A) :
    cosheafShiftMap (φ ≫ (geometricSmoothing ε).map ψ ≫
        (geometricSmoothingCompIso ε δ).hom.app A) =
      cosheafShiftMap φ ≫ (smoothing ε).map (cosheafShiftMap ψ) ≫
        (smoothingCompIso ε δ).hom.app (cosheafFunctor.obj A).obj := by
  have hnat : (cosheafFunctor.map ((geometricSmoothing ε).map ψ)).hom ≫
      ((geometricSmoothingComparisonIso ε).hom.app ((geometricSmoothing δ).obj A)).hom =
        ((geometricSmoothingComparisonIso ε).hom.app B).hom ≫
          (smoothing ε).map (cosheafFunctor.map ψ).hom :=
    congrArg (fun f => f.hom) ((geometricSmoothingComparisonIso ε).hom.naturality ψ)
  have hsq := cosheafFunctor_map_geometricSmoothingCompIso_hom_app ε δ A
  have e1 : (cosheafFunctor.map (φ ≫ (geometricSmoothing ε).map ψ ≫
      (geometricSmoothingCompIso ε δ).hom.app A)).hom =
        (cosheafFunctor.map φ).hom ≫ (cosheafFunctor.map ((geometricSmoothing ε).map ψ)).hom ≫
          (cosheafFunctor.map ((geometricSmoothingCompIso ε δ).hom.app A)).hom := by
    rw [Functor.map_comp, Functor.map_comp]
    rfl
  -- `C φ ≫ C (U_ε ψ) ≫ C μ ≫ β^(ε+δ)`: the merged square `hsq` replaces `C μ ≫ β^(ε+δ)`,
  -- naturality `hnat` of `β^ε` moves `C (U_ε ψ)` past it, and `S_ε (C ψ ≫ β^δ)` is folded last.
  refine ((congrArg (· ≫ ((geometricSmoothingComparisonIso (ε + δ)).hom.app A).hom) e1).trans
    ((Category.assoc _ _ _).trans (congrArg ((cosheafFunctor.map φ).hom ≫ ·)
      ((Category.assoc _ _ _).trans (congrArg
        ((cosheafFunctor.map ((geometricSmoothing ε).map ψ)).hom ≫ ·) hsq))))).trans ?_
  refine (congrArg ((cosheafFunctor.map φ).hom ≫ ·)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hnat))).trans ?_
  refine (congrArg ((cosheafFunctor.map φ).hom ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine congrArg (((cosheafFunctor.map φ).hom ≫
    ((geometricSmoothingComparisonIso ε).hom.app B).hom) ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ (smoothingCompIso ε δ).hom.app (cosheafFunctor.obj A).obj)
    ((smoothing ε).map_comp _ _).symm

/-! ### Witness comparison and the distance inequality -/

namespace GeometricInterleaving

variable {ε : ℝ≥0}

/-- A geometric `ε`-interleaving gives a precosheaf `ε`-interleaving of the component
cosheaves, by the shifted maps. -/
def toCosheaf (i : GeometricInterleaving ε A B) :
    Interleaving ε (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj where
  φ := cosheafShiftMap i.φ
  ψ := cosheafShiftMap i.ψ
  φ_ψ := by rw [← cosheafShiftMap_comp, i.φ_ψ, cosheafShiftMap_unit]
  ψ_φ := by rw [← cosheafShiftMap_comp, i.ψ_φ, cosheafShiftMap_unit]

theorem toCosheaf_φ (i : GeometricInterleaving ε A B) : i.toCosheaf.φ = cosheafShiftMap i.φ :=
  rfl

theorem toCosheaf_ψ (i : GeometricInterleaving ε A B) : i.toCosheaf.ψ = cosheafShiftMap i.ψ :=
  rfl

theorem toCosheaf_symm (i : GeometricInterleaving ε A B) :
    i.symm.toCosheaf = i.toCosheaf.symm :=
  Interleaving.ext rfl rfl

end GeometricInterleaving

/-- **`d_cosheaf ≤ d_geo`**: the interleaving distance of the underlying component precosheaves is
at most the geometric interleaving distance. -/
theorem interleavingDistance_cosheafFunctor_le_geometricInterleavingDistance (A B : RGraphCat) :
    interleavingDistance (cosheafFunctor.obj A).obj (cosheafFunctor.obj B).obj ≤
      geometricInterleavingDistance A B :=
  le_iInf₂ fun _ ⟨i⟩ => i.toCosheaf.interleavingDistance_le

end RGraph

end

end TDA.Reeb
