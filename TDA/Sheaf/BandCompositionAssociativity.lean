import TDA.Sheaf.BandCompositionUnit

/-!
# Associativity of band composition

The two orders of composition are compared on the space of four-point band chains.
The adjoints of both composites there are the same composite of three transported derived
counits. The section that inserts the second point and the invertible restriction of the
sum detect equality of the original maps. The associativity law on the bounded derived
category follows through its faithful inclusion.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace

namespace TDA.Sheaf.BandConvolution

section pasting

variable (k : Type) [Ring k]
variable {X Y W R : TopCat.{0}}
  [HasDerivedCategory (X.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (Y.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (W.Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (R.Sheaf (ModuleCat.{0} k))]

-- Taking the adjoint of a correspondence restriction followed by a direct image.
private lemma corrRestr_map_adjoint (j : X ⟶ Y) (p q : Y ⟶ R)
    (M : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k)))
    {N : DerivedCategory.Plus (X.Sheaf (ModuleCat.{0} k))}
    (φ : (pullbackPlus k (j ≫ p)).obj M ⟶ N) :
    (pullbackPlus k (j ≫ q)).map ((corrRestr k j p q).app M ≫
          (pushforwardPlus k (j ≫ q)).map φ) ≫
        (derivedCounit k (j ≫ q)).app N =
      (transportCounit k j p q).app M ≫ φ := by
  have h := (derivedAdjunction k (j ≫ q)).homEquiv_naturality_right_symm
    ((corrRestr k j p q).app M) φ
  simp only [Adjunction.homEquiv_counit, derivedAdjunction_counit] at h
  rw [h, corrRestr_counit, transportCounit_app]
  simp only [Category.assoc, Functor.comp_obj]

-- Transport in the inverse images of the two legs of a correspondence.
private def pullbackHom (i : W ⟶ X) (p q : X ⟶ R)
    {M N : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k))}
    (φ : (pullbackPlus k q).obj M ⟶ (pullbackPlus k p).obj N) :
    (pullbackPlus k (i ≫ q)).obj M ⟶ (pullbackPlus k (i ≫ p)).obj N :=
  (pullbackPlusCompIso k i q).inv.app M ≫
    (pullbackPlus k i).map φ ≫ (pullbackPlusCompIso k i p).hom.app N

private lemma pullbackHom_comp (i : W ⟶ X) (p q u : X ⟶ R)
    {M N L : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k))}
    (φ : (pullbackPlus k q).obj M ⟶ (pullbackPlus k p).obj N)
    (ψ : (pullbackPlus k p).obj N ⟶ (pullbackPlus k u).obj L) :
    pullbackHom k i u q (φ ≫ ψ) = pullbackHom k i p q φ ≫ pullbackHom k i u p ψ := by
  simp only [pullbackHom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private lemma pullbackHom_map (i : W ⟶ X) (p : X ⟶ R)
    {M N : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k))} (f : M ⟶ N) :
    pullbackHom k i p p ((pullbackPlus k p).map f) =
      (pullbackPlus k (i ≫ p)).map f := by
  have n := (pullbackPlusCompIso k i p).hom.naturality f
  simp only [Functor.comp_map] at n
  simp only [pullbackHom, n, Iso.inv_hom_id_app_assoc]

private lemma pullbackHom_transportCounit (i : W ⟶ X) (j : X ⟶ Y) (p q : Y ⟶ R)
    (M : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k))) :
    pullbackHom k i (j ≫ p) (j ≫ q) ((transportCounit k j p q).app M) =
      (transportCounit k (i ≫ j) p q).app M := by
  rw [pullbackHom, transportCounit_app, transportCounit_app, ← cancel_epi
    ((pullbackPlusCompIso k i (j ≫ q)).hom.app
      ((pullbackPlus k p ⋙ pushforwardPlus k q).obj M))]
  simp only [Iso.hom_inv_id_app_assoc]
  exact (pullbackPlusCompIso_transport k i j q p
    ((pullbackPlus k p ⋙ pushforwardPlus k q).obj M) M
    ((derivedCounit k q).app ((pullbackPlus k p).obj M))).symm

-- A split projection detects equality of adjoints along the output map.
private lemma eq_of_transportCounit_eq (i : W ⟶ X) (s : X ⟶ W) (hs : s ≫ i = 𝟙 X)
    (j : X ⟶ Y) (p q : Y ⟶ R) (M : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k)))
    [Mono ((corrRestr k j p q).app M)]
    {N : DerivedCategory.Plus (R.Sheaf (ModuleCat.{0} k))}
    {f g : N ⟶ (pullbackPlus k p ⋙ pushforwardPlus k q).obj M}
    (h : (pullbackPlus k ((i ≫ j) ≫ q)).map f ≫ (transportCounit k (i ≫ j) p q).app M =
      (pullbackPlus k ((i ≫ j) ≫ q)).map g ≫ (transportCounit k (i ≫ j) p q).app M) :
    f = g := by
  have e := congrArg (pullbackHom k s ((i ≫ j) ≫ p) ((i ≫ j) ≫ q)) h
  simp only [pullbackHom_comp, pullbackHom_map, pullbackHom_transportCounit] at e
  let P (r : X ⟶ Y) : Prop :=
    (pullbackPlus k (r ≫ q)).map f ≫ (transportCounit k r p q).app M =
      (pullbackPlus k (r ≫ q)).map g ≫ (transportCounit k r p q).app M
  have er : s ≫ i ≫ j = j := by rw [← Category.assoc, hs, Category.id_comp]
  have hj : P j := (congrArg P er).mp e
  apply (cancel_mono ((corrRestr k j p q).app M)).mp
  apply ((derivedAdjunction k (j ≫ q)).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, derivedAdjunction_counit, Functor.map_comp,
    Category.assoc, corrRestr_counit]
  simpa only [P, transportCounit_app, Functor.comp_obj] using hj

end pasting

section fourPoints

-- The iterated fibre product of three bands over the line.
private abbrev FourChain (a b c : ℝ) : TopCat.{0} :=
  TopCat.of { w : ℝ × ℝ × ℝ × ℝ |
    dist w.1 w.2.1 ≤ a ∧ dist w.2.1 w.2.2.1 ≤ b ∧ dist w.2.2.1 w.2.2.2 ≤ c }

private def firstThree (a b c : ℝ) : FourChain a b c ⟶ Z a b :=
  TopCat.ofHom ⟨fun w => ⟨(w.1.1, w.1.2.1, w.1.2.2.1), w.2.1, w.2.2.1⟩, by fun_prop⟩

private def lastThree (a b c : ℝ) : FourChain a b c ⟶ Z b c :=
  TopCat.ofHom ⟨fun w => ⟨w.1.2, w.2.2⟩, by fun_prop⟩

private def forgetSecond (a b c : ℝ) : FourChain a b c ⟶ Z (a + b) c :=
  TopCat.ofHom ⟨fun w => ⟨(w.1.1, w.1.2.2.1, w.1.2.2.2),
    (dist_triangle _ _ _).trans (add_le_add w.2.1 w.2.2.1), w.2.2.2⟩, by fun_prop⟩

private def forgetThird (a b c : ℝ) : FourChain a b c ⟶ Z a (b + c) :=
  TopCat.ofHom ⟨fun w => ⟨(w.1.1, w.1.2.1, w.1.2.2.2), w.2.1,
    (dist_triangle _ _ _).trans (add_le_add w.2.2.1 w.2.2.2)⟩, by fun_prop⟩

-- Insert the lower endpoint of the allowable interval for the missing coordinate.
private def insertSecond {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Z (a + b) c ⟶ FourChain a b c := by
  let lift (w : Z (a + b) c) : Z a b :=
    fibreEmb₁₃ a b (pr₁₂ (a + b) c w) ⟨_, le_rfl, lo_le_hi_pr₁₃ ha hb _⟩
  refine TopCat.ofHom ⟨fun w => ⟨(w.1.1, (lift w).1.2.1, w.1.2.1, w.1.2.2),
    (lift w).2.1, (lift w).2.2, w.2.2⟩, ?_⟩
  apply Continuous.subtype_mk
  change Continuous (fun w : Z (a + b) c =>
    (w.1.1, max (w.1.1 - a) (w.1.2.1 - b), w.1.2.1, w.1.2.2))
  fun_prop

private theorem insertSecond_forgetSecond {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    insertSecond (c := c) ha hb ≫ forgetSecond a b c = 𝟙 _ :=
  TopCat.ext fun _ => Subtype.ext rfl

end fourPoints

variable (k : Type) [Ring k] [HasDerivedCategory (realLine.Sheaf (ModuleCat.{0} k))]
  [∀ a : ℝ, HasDerivedCategory ((D a).Sheaf (ModuleCat.{0} k))]
  [∀ a b : ℝ, HasDerivedCategory ((Z a b).Sheaf (ModuleCat.{0} k))]
  [HasDerivedCategory (pt.Sheaf (ModuleCat.{0} k))]
  [∀ u v : ℝ, HasDerivedCategory ((TopCat.of (Set.Icc u v)).Sheaf (ModuleCat.{0} k))]

-- Pasting on the two-band correspondence, after taking the adjoint along its output map.
private lemma TCompOfEq_transportCounit {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (e : a + b = d) (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k (pr₁₃Of e ≫ q d)).map ((TCompOfEq k ha hb e).hom.app M) ≫
        (transportCounit k (pr₁₃Of e) (p d) (q d)).app M =
      (transportCounit k (pr₂₃ a b) (p b) (q b)).app ((T k a).obj M) ≫
        (transportCounit k (pr₁₂ a b) (p a) (q a)).app M := by
  subst e
  rw [TCompOfEq_rfl]
  have h := TComp_hom_app_TCompRestr_eq k ha hb M
  have e := congrArg (fun f =>
    (pullbackPlus k (pr₂₃ a b ≫ q b)).map f ≫ (derivedCounit k (pr₂₃ a b ≫ q b)).app
      ((pullbackPlus k (pr₁₂ a b ≫ p a)).obj M)) h
  change (pullbackPlus k (pr₁₃ a b ≫ q (a + b))).map
        ((TComp k ha hb).hom.app M ≫ (corrRestr k (pr₁₃ a b) (p (a + b)) (q (a + b))).app M) ≫
      (derivedCounit k (pr₁₃ a b ≫ q (a + b))).app
        ((pullbackPlus k (pr₁₃ a b ≫ p (a + b))).obj M) = _ at e
  rw [Functor.map_comp, Category.assoc, corrRestr_counit] at e
  have hCounit : TCompCounit k a b M = (transportCounit k (pr₁₂ a b) (p a) (q a)).app M :=
    (TCompCounitNT_app k a b M).symm
  have e' := e.trans (corrRestr_map_adjoint k (pr₂₃ a b) (p b) (q b) ((T k a).obj M)
    (TCompCounit k a b M))
  change (pullbackPlus k (pr₁₃ a b ≫ q (a + b))).map ((TComp k ha hb).hom.app M) ≫
    (transportCounit k (pr₁₃ a b) (p (a + b)) (q (a + b))).app M = _
  simpa only [hCounit, transportCounit_app, Functor.comp_obj] using e'

-- The same pasting after inverse image to a common space.
private lemma transportCounit_TCompOfEq {a b d : ℝ} {V : TopCat.{0}}
    [HasDerivedCategory (V.Sheaf (ModuleCat.{0} k))]
    (i : V ⟶ Z a b) (ha : 0 ≤ a) (hb : 0 ≤ b) (e : a + b = d)
    (M : DerivedCategory.Plus (realLine.Sheaf (ModuleCat.{0} k))) :
    (pullbackPlus k ((i ≫ pr₁₃Of e) ≫ q d)).map ((TCompOfEq k ha hb e).hom.app M) ≫
        (transportCounit k (i ≫ pr₁₃Of e) (p d) (q d)).app M =
      (transportCounit k (i ≫ pr₂₃ a b) (p b) (q b)).app ((T k a).obj M) ≫
        (transportCounit k (i ≫ pr₁₂ a b) (p a) (q a)).app M := by
  have h := congrArg (pullbackHom k i (pr₁₃Of e ≫ p d) (pr₁₃Of e ≫ q d))
    (TCompOfEq_transportCounit k ha hb e M)
  simp only [pullbackHom_comp, pullbackHom_map, pullbackHom_transportCounit] at h
  have h' := pullbackHom_comp k i (pr₂₃ a b ≫ p b) (pr₂₃ a b ≫ q b) (pr₁₂ a b ≫ p a)
    ((transportCounit k (pr₂₃ a b) (p b) (q b)).app ((T k a).obj M))
    ((transportCounit k (pr₁₂ a b) (p a) (q a)).app M)
  change _ = pullbackHom k i (pr₂₃ a b ≫ p b) (pr₂₃ a b ≫ q b) _ ≫
    pullbackHom k i (pr₁₂ a b ≫ p a) (pr₁₂ a b ≫ q a) _ at h'
  simp only [pullbackHom_transportCounit] at h'
  exact h.trans h'

/-- The two compositions of three nonnegative bands agree after the functor associator.
The target radius is `(a + b) + c`, with `TCompOfEq` identifying `a + (b + c)` with it. -/
theorem TComp_assoc_hom {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Functor.whiskerRight (TComp k ha hb).hom (T k c) ≫ (TComp k (add_nonneg ha hb) hc).hom =
      (Functor.associator (T k a) (T k b) (T k c)).hom ≫
        Functor.whiskerLeft (T k a) (TComp k hb hc).hom ≫
        (TCompOfEq k ha (add_nonneg hb hc) (add_assoc a b c).symm).hom := by
  refine NatTrans.ext (funext fun M => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp]
  let : HasDerivedCategory ((FourChain a b c).Sheaf (ModuleCat.{0} k)) :=
    HasDerivedCategory.standard _
  have := isIso_TCompRestr k (add_nonneg ha hb) hc
  have : Mono ((corrRestr k (pr₁₃ (a + b) c) (p (a + b + c)) (q (a + b + c))).app M) :=
    inferInstanceAs (Mono ((TCompRestr k (a + b) c).app M))
  apply eq_of_transportCounit_eq k (forgetSecond a b c) (insertSecond ha hb)
    (insertSecond_forgetSecond ha hb) (pr₁₃ (a + b) c) (p (a + b + c)) (q (a + b + c)) M
  have outerLeft := transportCounit_TCompOfEq k (forgetSecond a b c) (add_nonneg ha hb) hc rfl M
  rw [TCompOfEq_rfl] at outerLeft
  have outerRight := transportCounit_TCompOfEq k (forgetThird a b c) ha (add_nonneg hb hc)
    (add_assoc a b c).symm M
  have innerLeft := transportCounit_TCompOfEq k (firstThree a b c) ha hb rfl M
  rw [TCompOfEq_rfl] at innerLeft
  have innerRight := transportCounit_TCompOfEq k (lastThree a b c) hb hc rfl ((T k a).obj M)
  rw [TCompOfEq_rfl] at innerRight
  let output := pullbackPlus k ((forgetSecond a b c ≫ pr₁₃ (a + b) c) ≫ q (a + b + c))
  let counitC := transportCounit k (forgetSecond a b c ≫ pr₂₃ (a + b) c) (p c) (q c)
  let counitAB := (transportCounit k (forgetSecond a b c ≫ pr₁₂ (a + b) c)
    (p (a + b)) (q (a + b))).app M
  let counitA := (transportCounit k (forgetThird a b c ≫ pr₁₂ a (b + c)) (p a) (q a)).app M
  let ab := (TComp k ha hb).hom.app M
  let bc := (TComp k hb hc).hom.app ((T k a).obj M)
  have naturality := counitC.naturality ab
  simp only [Functor.map_comp, Category.assoc]
  have left := (congrArg (output.map ((T k c).map ab) ≫ ·) outerLeft).trans
    ((reassoc_of% naturality) counitAB)
  have left' := left.trans (congrArg (counitC.app ((T k a ⋙ T k b).obj M) ≫ ·) innerLeft)
  have right := (congrArg (output.map bc ≫ ·) outerRight).trans
    ((reassoc_of% innerRight) counitA)
  exact left'.trans (right.trans (Category.assoc _ _ counitA)).symm

/-- Associativity of the composition isomorphisms on the bounded derived category. -/
theorem TCompB_assoc_hom {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Functor.whiskerRight (TCompB k ha hb).hom (TB k c) ≫ (TCompB k (add_nonneg ha hb) hc).hom =
      (Functor.associator (TB k a) (TB k b) (TB k c)).hom ≫
        Functor.whiskerLeft (TB k a) (TCompB k hb hc).hom ≫
        (compIsoB k (TCompOfEq k ha (add_nonneg hb hc) (add_assoc a b c).symm)).hom := by
  apply eq_of_whiskerRight_boundedToPlus
  simp only [Functor.whiskerRight_comp, whiskerRight_whiskerRight_restrictBounded,
    whiskerRight_compIsoB_hom]
  have h := congrArg (Functor.whiskerLeft (boundedToPlus _)) (TComp_assoc_hom k ha hb hc)
  simp only [Functor.whiskerLeft_comp] at h
  have hbc := congrArg (Functor.whiskerLeft (TB k a)) (whiskerRight_TCompB_hom k hb hc)
  have e := hbc.trans (whiskerLeft_restrictBounded_whiskerLeft (T k a) (preservesBounded_T k a)
    (TComp k hb hc).hom)
  exact h.trans (congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) e rfl)).symm

end TDA.Sheaf.BandConvolution
