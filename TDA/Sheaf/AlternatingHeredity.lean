import TDA.Sheaf.AlternatingDiagram
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Heredity of finite alternating diagrams

For a vertex `i` of the oriented path, the left adjoint of evaluation at `i` sends a vector
space `V` to the diagram `P_i ⊗ V`, whose value at `t` has one copy of `V` for each path from
`i` to `t`; `P_i = P_i ⊗ k` is the representable projective `k[paths i → −]`. The evaluation
Hom adjunction `Hom(P_i ⊗ V, X) ≃ Hom(V, X_i)` makes every `P_i ⊗ V` projective.

Every diagram `M` has the standard resolution
`0 → ⊕_(a : i → j) P_j ⊗ M_i → ⊕_i P_i ⊗ M_i → M → 0`. The differential sends `u ∈ M_i` in
the slot of an arrow `a : i → j` to `u` in its own path slot `a` of `P_i ⊗ M_i` and to
`-M(a) u` in the main slot (the identity path) of `P_j ⊗ M_j`; the augmentation is `M(p)` on
the slot of each path `p`. The resolution splits at every vertex, by a contracting map
defined by recursion on paths, so it is short exact. Both terms are projective, so every
diagram has projective dimension at most one and `Ext^m` vanishes for `m ≥ 2`.
-/

universe u w

namespace TDA.Sheaf.AlternatingDiagram

open CategoryTheory Limits Abelian

variable {n : ℕ} {k : Type u} [Field k] {o : Fin n → Bool}

instance hasFiniteBiproducts_diagram : HasFiniteBiproducts (Diagram k o) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-! ### Path tensors -/

variable (k o) in
/-- The left adjoint of evaluation at `i`: the diagram `P_i ⊗ V`, whose value at `t` is a
copy of `V` for each path from `i` to `t`. -/
noncomputable abbrev pathTensor (i : Fin (n + 1)) : ModuleCat.{u} k ⥤ Diagram k o :=
  evaluationLeftAdjoint (ModuleCat.{u} k) (vtx o i)

variable (k o) in
/-- The evaluation Hom adjunction `Hom(P_i ⊗ V, X) ≃ Hom(V, X_i)`. -/
noncomputable def pathTensorAdjunction (i : Fin (n + 1)) :
    pathTensor k o i ⊣ (evaluation (Paths (Vertex o)) (ModuleCat.{u} k)).obj (vtx o i) :=
  evaluationAdjunctionRight (ModuleCat.{u} k) (vtx o i)

/-- `P_i ⊗ V` is projective for every vector space `V`. -/
instance projective_pathTensor (i : Fin (n + 1)) (V : ModuleCat.{u} k) :
    Projective ((pathTensor k o i).obj V) :=
  (pathTensorAdjunction k o i).map_projective V
    (ModuleCat.projective_of_free (Module.Free.chooseBasis k V))

/-- The copy of `V` at a path `p : i ⟶ t` in `P_i ⊗ V`. -/
noncomputable def pathSlot (i : Fin (n + 1)) (V : ModuleCat.{u} k) {t : Paths (Vertex o)}
    (p : vtx o i ⟶ t) : V ⟶ ((pathTensor k o i).obj V).obj t :=
  Sigma.ι (fun _ : vtx o i ⟶ t => V) p

/-- A map out of `(P_i ⊗ V)_t` from one map out of `V` per path `i ⟶ t`. -/
noncomputable def pathDesc (i : Fin (n + 1)) (V : ModuleCat.{u} k) {t : Paths (Vertex o)}
    {X : ModuleCat.{u} k} (D : (vtx o i ⟶ t) → (V ⟶ X)) :
    ((pathTensor k o i).obj V).obj t ⟶ X :=
  Sigma.desc D

@[simp]
theorem pathSlot_pathDesc (i : Fin (n + 1)) (V : ModuleCat.{u} k) {t : Paths (Vertex o)}
    {X : ModuleCat.{u} k} (D : (vtx o i ⟶ t) → (V ⟶ X)) (p : vtx o i ⟶ t) :
    pathSlot i V p ≫ pathDesc i V D = D p :=
  Sigma.ι_comp_desc _ _

theorem pathTensor_hom_ext (i : Fin (n + 1)) (V : ModuleCat.{u} k) {t : Paths (Vertex o)}
    {X : ModuleCat.{u} k} {f g : ((pathTensor k o i).obj V).obj t ⟶ X}
    (h : ∀ p : vtx o i ⟶ t, pathSlot i V p ≫ f = pathSlot i V p ≫ g) : f = g :=
  Sigma.hom_ext _ _ h

/-- The arrows of `P_i ⊗ V` compose paths. -/
@[simp]
theorem pathSlot_map (i : Fin (n + 1)) (V : ModuleCat.{u} k) {t t' : Paths (Vertex o)}
    (p : vtx o i ⟶ t) (q : t ⟶ t') :
    pathSlot i V p ≫ ((pathTensor k o i).obj V).map q = pathSlot i V (p ≫ q) := by
  unfold pathSlot
  simp only [evaluationLeftAdjoint_obj_map]
  exact Sigma.ι_comp_desc _ _

/-- The adjunction restricts a morphism `P_i ⊗ V ⟶ X` to the slot of the identity path. -/
theorem pathTensorAdjunction_homEquiv_apply (i : Fin (n + 1)) (V : ModuleCat.{u} k)
    (X : Diagram k o) (f : (pathTensor k o i).obj V ⟶ X) :
    (pathTensorAdjunction k o i).homEquiv V X f = pathSlot i V (𝟙 _) ≫ f.app (vtx o i) := rfl

/-- The morphism `P_i ⊗ V ⟶ X` adjoint to `f : V ⟶ X_i` sends the slot of `p` by `X(p) ∘ f`. -/
@[simp]
theorem pathSlot_homEquiv_symm_app (i : Fin (n + 1)) (V : ModuleCat.{u} k)
    (X : Diagram k o) (f : V ⟶ X.obj (vtx o i)) {t : Paths (Vertex o)} (p : vtx o i ⟶ t) :
    pathSlot i V p ≫ (((pathTensorAdjunction k o i).homEquiv V X).symm f).app t =
      f ≫ X.map p := by
  simp only [pathSlot, pathTensorAdjunction, evaluationAdjunctionRight,
    Adjunction.mkOfHomEquiv_homEquiv]
  exact Sigma.ι_comp_desc _ _

/-! ### Representables and the free description -/

variable (k o) in
/-- The representable projective `P_i = k[paths i → −]`, the path tensor of the field. -/
noncomputable abbrev representable (i : Fin (n + 1)) : Diagram k o :=
  (pathTensor k o i).obj (ModuleCat.of k k)

open Classical in
/-- `(P_i ⊗ V)_t` is the direct sum of one copy of `V` for each path from `i` to `t`. -/
noncomputable def pathTensorObjIso (i : Fin (n + 1)) (V : ModuleCat.{u} k)
    (t : Paths (Vertex o)) :
    ((pathTensor k o i).obj V).obj t ≅ ModuleCat.of k (DirectSum (vtx o i ⟶ t) fun _ => V) :=
  ModuleCat.coprodIsoDirectSum (fun _ : vtx o i ⟶ t => V)

open Classical in
/-- `(P_i ⊗ V)_t` is the space of finitely supported `V`-valued functions on the paths from
`i` to `t`; for `V = k` it is the free vector space `k[paths i → t]`. -/
noncomputable def pathTensorObjEquiv (i : Fin (n + 1)) (V : ModuleCat.{u} k)
    (t : Paths (Vertex o)) : ((pathTensor k o i).obj V).obj t ≃ₗ[k] ((vtx o i ⟶ t) →₀ V) :=
  (pathTensorObjIso i V t).toLinearEquiv ≪≫ₗ (finsuppLequivDFinsupp k).symm

/-- The slot of a path `p` is the single function at `p`. -/
theorem pathTensorObjEquiv_pathSlot (i : Fin (n + 1)) (V : ModuleCat.{u} k)
    {t : Paths (Vertex o)} (p : vtx o i ⟶ t) (v : V) :
    pathTensorObjEquiv i V t ((pathSlot i V p).hom v) = Finsupp.single p v := by
  classical
  have h₁ : (pathTensorObjIso i V t).hom.hom ((pathSlot i V p).hom v) =
      DirectSum.lof k (vtx o i ⟶ t) (fun _ => V) p v :=
    ModuleCat.ι_coprodIsoDirectSum_hom_apply (fun _ : vtx o i ⟶ t => V) p v
  rw [pathTensorObjEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, h₁,
    finsuppLequivDFinsupp_symm_apply]
  exact DFinsupp.toFinsupp_single p v

/-- Under `pathTensorObjEquiv`, the arrows of `P_i ⊗ V` push functions forward along
composition of paths. -/
theorem pathTensorObjEquiv_map (i : Fin (n + 1)) (V : ModuleCat.{u} k)
    {t t' : Paths (Vertex o)} (q : t ⟶ t') (x : ((pathTensor k o i).obj V).obj t) :
    pathTensorObjEquiv i V t' ((((pathTensor k o i).obj V).map q).hom x) =
      Finsupp.mapDomain (· ≫ q) (pathTensorObjEquiv i V t x) := by
  have h : ModuleCat.ofHom ((pathTensorObjEquiv i V t').toLinearMap ∘ₗ
        (((pathTensor k o i).obj V).map q).hom) =
      ModuleCat.ofHom ((Finsupp.lmapDomain V k (· ≫ q)) ∘ₗ
        (pathTensorObjEquiv i V t).toLinearMap) := by
    refine pathTensor_hom_ext i V fun p => ?_
    ext v
    have hmap := congrArg (fun f => ModuleCat.Hom.hom f v) (pathSlot_map i V p q)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hmap
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.coe_coe, hmap, pathTensorObjEquiv_pathSlot, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
  exact congrArg (fun φ => φ.hom x) h

/-- The Yoneda property of `P_i`: morphisms `P_i ⟶ X` are the vectors of `X_i`, through the
image of `1` in the slot of the identity path. -/
noncomputable def representableHomEquiv (i : Fin (n + 1)) (X : Diagram k o) :
    (representable k o i ⟶ X) ≃ X.obj (vtx o i) :=
  ((pathTensorAdjunction k o i).homEquiv _ _).trans
    (ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf k k _).toEquiv)

theorem representableHomEquiv_apply (i : Fin (n + 1)) (X : Diagram k o)
    (f : representable k o i ⟶ X) :
    representableHomEquiv i X f =
      (f.app (vtx o i)).hom ((pathSlot i (ModuleCat.of k k) (𝟙 _)).hom 1) := rfl

/-! ### Finite sums of path tensors -/

section Sums

variable {J : Type} [Fintype J] (σ : J → Fin (n + 1)) (V : J → ModuleCat.{u} k)

/-- The finite sum `⊕_j P_(σ j) ⊗ V_j`. -/
noncomputable abbrev sumTensor : Diagram k o := ⨁ fun j => (pathTensor k o (σ j)).obj (V j)

/-- A finite sum of path tensors is projective. -/
instance projective_sumTensor : Projective (sumTensor (o := o) σ V) where
  factors f e _ := ⟨biproduct.desc fun j => Projective.factorThru
      (biproduct.ι (fun j => (pathTensor k o (σ j)).obj (V j)) j ≫ f) e,
    biproduct.hom_ext' _ _ fun j => by simp⟩

/-- The copy of `V_j` in `⊕_j P_(σ j) ⊗ V_j` at a path `p : σ j ⟶ t`. -/
noncomputable def sumSlot (j : J) {t : Paths (Vertex o)} (p : vtx o (σ j) ⟶ t) :
    V j ⟶ (sumTensor (o := o) σ V).obj t :=
  pathSlot (σ j) (V j) p ≫ (biproduct.ι (fun j => (pathTensor k o (σ j)).obj (V j)) j).app t

theorem sumSlot_map (j : J) {t t' : Paths (Vertex o)} (p : vtx o (σ j) ⟶ t) (q : t ⟶ t') :
    sumSlot σ V j p ≫ (sumTensor σ V).map q = sumSlot σ V j (p ≫ q) := by
  unfold sumSlot sumTensor
  rw [Category.assoc, ← NatTrans.naturality, ← Category.assoc, pathSlot_map]

theorem sumTensor_hom_ext {t : Paths (Vertex o)} {X : ModuleCat.{u} k}
    {f g : (sumTensor (o := o) σ V).obj t ⟶ X}
    (h : ∀ j (p : vtx o (σ j) ⟶ t), sumSlot σ V j p ≫ f = sumSlot σ V j p ≫ g) : f = g := by
  have htot : ∀ φ : (sumTensor (o := o) σ V).obj t ⟶ X,
      φ = ∑ j, (biproduct.π (fun j => (pathTensor k o (σ j)).obj (V j)) j).app t ≫
        (biproduct.ι (fun j => (pathTensor k o (σ j)).obj (V j)) j).app t ≫ φ := by
    intro φ
    have := congrArg (fun ψ => ψ.app t ≫ φ)
      (biproduct.total (f := fun j => (pathTensor k o (σ j)).obj (V j)))
    simp only [NatTrans.app_sum, Preadditive.sum_comp, NatTrans.comp_app, Category.assoc,
      NatTrans.id_app, Category.id_comp] at this
    exact this.symm
  rw [htot f, htot g]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact pathTensor_hom_ext _ _ fun p => by simpa only [sumSlot, Category.assoc] using h j p

/-- A map out of `(⊕_j P_(σ j) ⊗ V_j)_t` from one map out of `V_j` per path `σ j ⟶ t`. -/
noncomputable def sumDesc {t : Paths (Vertex o)} {X : ModuleCat.{u} k}
    (D : ∀ j, (vtx o (σ j) ⟶ t) → (V j ⟶ X)) : (sumTensor (o := o) σ V).obj t ⟶ X :=
  ∑ j, (biproduct.π (fun j => (pathTensor k o (σ j)).obj (V j)) j).app t ≫
    pathDesc (σ j) (V j) (D j)

@[simp]
theorem sumSlot_sumDesc {t : Paths (Vertex o)} {X : ModuleCat.{u} k}
    (D : ∀ j, (vtx o (σ j) ⟶ t) → (V j ⟶ X)) (i : J) (p : vtx o (σ i) ⟶ t) :
    sumSlot σ V i p ≫ sumDesc σ V D = D i p := by
  unfold sumSlot sumDesc
  rw [Preadditive.comp_sum, Finset.sum_eq_single i]
  · rw [Category.assoc, ← Category.assoc
      ((biproduct.ι (fun j => (pathTensor k o (σ j)).obj (V j)) i).app t), ← NatTrans.comp_app,
      biproduct.ι_π_self, NatTrans.id_app, Category.id_comp, pathSlot_pathDesc]
  · intro j _ hj
    rw [Category.assoc, ← Category.assoc
      ((biproduct.ι (fun j => (pathTensor k o (σ j)).obj (V j)) i).app t), ← NatTrans.comp_app,
      biproduct.ι_π_ne _ (Ne.symm hj)]
    simp
  · simp

/-- The morphism `⊕_j P_(σ j) ⊗ V_j ⟶ X` adjoint to maps `V_j ⟶ X_(σ j)`. -/
noncomputable def sumTensorDesc (X : Diagram k o) (φ : ∀ j, V j ⟶ X.obj (vtx o (σ j))) :
    sumTensor σ V ⟶ X :=
  biproduct.desc fun j => ((pathTensorAdjunction k o (σ j)).homEquiv _ _).symm (φ j)

@[simp]
theorem sumSlot_sumTensorDesc_app (X : Diagram k o) (φ : ∀ j, V j ⟶ X.obj (vtx o (σ j)))
    (j : J) {t : Paths (Vertex o)} (p : vtx o (σ j) ⟶ t) :
    sumSlot σ V j p ≫ (sumTensorDesc σ V X φ).app t = φ j ≫ X.map p := by
  unfold sumSlot sumTensorDesc
  rw [Category.assoc, ← NatTrans.comp_app, biproduct.ι_desc, pathSlot_homEquiv_symm_app]

end Sums

/-! ### The standard resolution -/

/-- Induction on paths from a fixed vertex, extending by one generating arrow at a time. -/
private theorem path_induction {i : Fin (n + 1)}
    {P : ∀ {t : Paths (Vertex o)}, (vtx o i ⟶ t) → Prop} (id : P (𝟙 (vtx o i)))
    (comp : ∀ {j l : Fin (n + 1)} (p : vtx o i ⟶ vtx o j) (h : Arrow o j l), P p →
      P (p ≫ gen h)) {t : Paths (Vertex o)} (p : vtx o i ⟶ t) : P p :=
  Paths.induction_fixed_source P id (fun p q ih => comp p q.down ih) p

/-- Induction on paths from a fixed vertex to a vertex, extending by one generating arrow at a
time. -/
private theorem path_induction' {i : Fin (n + 1)}
    {P : ∀ {t : Fin (n + 1)}, (vtx o i ⟶ vtx o t) → Prop} (id : P (𝟙 (vtx o i)))
    (comp : ∀ {j l : Fin (n + 1)} (p : vtx o i ⟶ vtx o j) (h : Arrow o j l), P p →
      P (p ≫ gen h)) {t : Fin (n + 1)} (p : vtx o i ⟶ vtx o t) : P p :=
  path_induction (P := fun {t} p => P (t := t) p) id comp p

/-- The arrows of the oriented path, indexed by their source and target. -/
abbrev Edge (o : Fin n → Bool) : Type := {e : Fin (n + 1) × Fin (n + 1) // Arrow o e.1 e.2}

variable (M : Diagram k o)

/-- The middle term `⊕_i P_i ⊗ M_i` of the standard resolution. -/
noncomputable def resolutionMiddle : Diagram k o :=
  sumTensor (fun i : Fin (n + 1) => i) fun i => M.obj (vtx o i)

/-- The left term `⊕_(a : i → j) P_j ⊗ M_i` of the standard resolution. -/
noncomputable def resolutionLeft : Diagram k o :=
  sumTensor (fun e : Edge o => e.1.2) fun e => M.obj (vtx o e.1.1)

instance projective_resolutionMiddle : Projective (resolutionMiddle M) :=
  projective_sumTensor _ _

instance projective_resolutionLeft : Projective (resolutionLeft M) := projective_sumTensor _ _

/-- The copy of `M_i` in the middle term at a path `p : i ⟶ t`; the path `𝟙 i` gives the main
slot of `i`. -/
noncomputable def middleSlot (i : Fin (n + 1)) {t : Paths (Vertex o)} (p : vtx o i ⟶ t) :
    M.obj (vtx o i) ⟶ (resolutionMiddle M).obj t :=
  sumSlot (fun i : Fin (n + 1) => i) (fun i => M.obj (vtx o i)) i p

/-- The copy of `M_i` in the left term at an arrow `i → j` and a path `q : j ⟶ t`. -/
noncomputable def leftSlot (e : Edge o) {t : Paths (Vertex o)} (q : vtx o e.1.2 ⟶ t) :
    M.obj (vtx o e.1.1) ⟶ (resolutionLeft M).obj t :=
  sumSlot (fun e : Edge o => e.1.2) (fun e => M.obj (vtx o e.1.1)) e q

theorem middleSlot_map (i : Fin (n + 1)) {t t' : Paths (Vertex o)} (p : vtx o i ⟶ t)
    (q : t ⟶ t') : middleSlot M i p ≫ (resolutionMiddle M).map q = middleSlot M i (p ≫ q) :=
  sumSlot_map (fun i : Fin (n + 1) => i) (fun i => M.obj (vtx o i)) i p q

theorem leftSlot_map (e : Edge o) {t t' : Paths (Vertex o)} (p : vtx o e.1.2 ⟶ t)
    (q : t ⟶ t') : leftSlot M e p ≫ (resolutionLeft M).map q = leftSlot M e (p ≫ q) :=
  sumSlot_map (fun e : Edge o => e.1.2) (fun e => M.obj (vtx o e.1.1)) e p q

theorem middle_hom_ext {t : Paths (Vertex o)} {X : ModuleCat.{u} k}
    {f g : (resolutionMiddle M).obj t ⟶ X}
    (h : ∀ i (p : vtx o i ⟶ t), middleSlot M i p ≫ f = middleSlot M i p ≫ g) : f = g :=
  sumTensor_hom_ext _ _ h

theorem left_hom_ext {t : Paths (Vertex o)} {X : ModuleCat.{u} k}
    {f g : (resolutionLeft M).obj t ⟶ X}
    (h : ∀ e (q : vtx o e.1.2 ⟶ t), leftSlot M e q ≫ f = leftSlot M e q ≫ g) : f = g :=
  sumTensor_hom_ext _ _ h

/-- The component of the differential at an arrow `a : i → j`: a vector `u` of `M_i` goes to
its own path slot `a` with sign `+` and to `M(a) u` in the main slot of `j` with sign `−`. -/
noncomputable def differentialComponent (e : Edge o) :
    M.obj (vtx o e.1.1) ⟶ (resolutionMiddle M).obj (vtx o e.1.2) :=
  middleSlot M e.1.1 (gen e.2) - M.map (gen e.2) ≫ middleSlot M e.1.2 (𝟙 _)

/-- The differential `⊕_(a : i → j) P_j ⊗ M_i ⟶ ⊕_i P_i ⊗ M_i`. -/
noncomputable def resolutionDifferential : resolutionLeft M ⟶ resolutionMiddle M :=
  sumTensorDesc _ _ _ (differentialComponent M)

/-- The augmentation `⊕_i P_i ⊗ M_i ⟶ M`: the counit `M(p)` on the slot of each path `p`. -/
noncomputable def resolutionAugmentation : resolutionMiddle M ⟶ M :=
  sumTensorDesc _ _ _ fun _ => 𝟙 _

/-- The differential on the slot of an arrow `a : i → j` and a path `q : j ⟶ t`. -/
theorem leftSlot_resolutionDifferential_app (e : Edge o) {t : Paths (Vertex o)}
    (q : vtx o e.1.2 ⟶ t) :
    leftSlot M e q ≫ (resolutionDifferential M).app t =
      middleSlot M e.1.1 (gen e.2 ≫ q) - M.map (gen e.2) ≫ middleSlot M e.1.2 q := by
  have := sumSlot_sumTensorDesc_app (fun e : Edge o => e.1.2) (fun e => M.obj (vtx o e.1.1))
    (resolutionMiddle M) (differentialComponent M) e q
  refine this.trans ?_
  rw [differentialComponent, Preadditive.sub_comp, Category.assoc, middleSlot_map,
    middleSlot_map, Category.id_comp]

/-- The augmentation on the slot of a path `p : i ⟶ t` is `M(p)`. -/
theorem middleSlot_resolutionAugmentation_app (i : Fin (n + 1)) {t : Paths (Vertex o)}
    (p : vtx o i ⟶ t) : middleSlot M i p ≫ (resolutionAugmentation M).app t = M.map p :=
  (sumSlot_sumTensorDesc_app (fun i : Fin (n + 1) => i) (fun i => M.obj (vtx o i)) M
    (fun _ => 𝟙 _) i p).trans (Category.id_comp _)

theorem resolutionDifferential_comp_augmentation :
    resolutionDifferential M ≫ resolutionAugmentation M = 0 := by
  ext t : 2
  apply left_hom_ext
  intro e q
  rw [NatTrans.comp_app, ← Category.assoc, leftSlot_resolutionDifferential_app,
    Preadditive.sub_comp, Category.assoc, middleSlot_resolutionAugmentation_app,
    middleSlot_resolutionAugmentation_app, Functor.map_comp, sub_self]
  simp

/-- The standard resolution `⊕_(a : i → j) P_j ⊗ M_i ⟶ ⊕_i P_i ⊗ M_i ⟶ M`. -/
noncomputable def resolution : ShortComplex (Diagram k o) :=
  ShortComplex.mk (resolutionDifferential M) (resolutionAugmentation M)
    (resolutionDifferential_comp_augmentation M)

@[simp] theorem resolution_X₁ : (resolution M).X₁ = resolutionLeft M := rfl

@[simp] theorem resolution_X₂ : (resolution M).X₂ = resolutionMiddle M := rfl

@[simp] theorem resolution_X₃ : (resolution M).X₃ = M := rfl

@[simp] theorem resolution_f : (resolution M).f = resolutionDifferential M := rfl

@[simp] theorem resolution_g : (resolution M).g = resolutionAugmentation M := rfl

/-- The pointwise contracting map of the resolution, by recursion on paths: the slot of a path
`p` goes to the sum, over the arrows `a` of `p`, of the slot of `a` and the rest of `p` after
`a`, applied to `M` of the part of `p` before `a`. -/
noncomputable def resolutionLift (i : Fin (n + 1)) :
    ∀ {t : Paths (Vertex o)}, (vtx o i ⟶ t) → (M.obj (vtx o i) ⟶ (resolutionLeft M).obj t)
  | _, Quiver.Path.nil => 0
  | _, Quiver.Path.cons p e =>
      resolutionLift i p ≫ (resolutionLeft M).map (gen e.down) +
        M.map p ≫ leftSlot M ⟨(_, _), e.down⟩ (𝟙 _)

@[simp]
theorem resolutionLift_id (i : Fin (n + 1)) : resolutionLift M i (𝟙 (vtx o i)) = 0 := rfl

theorem resolutionLift_comp_gen (i : Fin (n + 1)) {j l : Fin (n + 1)} (p : vtx o i ⟶ vtx o j)
    (h : Arrow o j l) :
    resolutionLift M i (p ≫ gen h) =
      resolutionLift M i p ≫ (resolutionLeft M).map (gen h) +
        M.map p ≫ leftSlot M ⟨(j, l), h⟩ (𝟙 _) := rfl

/-- The contracting map undoes the differential on the slot of an arrow `a : i → j` and a path
`q : j ⟶ t`. -/
theorem resolutionLift_differential (e : Edge o) {t : Paths (Vertex o)}
    (q : vtx o e.1.2 ⟶ t) :
    resolutionLift M e.1.1 (gen e.2 ≫ q) - M.map (gen e.2) ≫ resolutionLift M e.1.2 q =
      leftSlot M e q := by
  obtain ⟨⟨i, j⟩, h⟩ := e
  induction q using path_induction with
  | id =>
    erw [Category.comp_id, resolutionLift_id, Limits.comp_zero, sub_zero]
    erw [resolutionLift_comp_gen M i (𝟙 (vtx o i)) h, resolutionLift_id, Limits.zero_comp,
      zero_add, M.map_id, Category.id_comp]
  | comp q f ih =>
    erw [← Category.assoc, resolutionLift_comp_gen, resolutionLift_comp_gen]
    rw [← leftSlot_map, ← ih, Preadditive.sub_comp, M.map_comp, Preadditive.comp_add]
    simp only [Category.assoc]
    abel

/-- On the slot of a path `p : i ⟶ t`, the contracting map followed by the differential is the
slot itself minus the main slot of `M(p)`. -/
theorem resolutionLift_comp_differential (i : Fin (n + 1)) {t : Fin (n + 1)}
    (p : vtx o i ⟶ vtx o t) :
    resolutionLift M i p ≫ (resolutionDifferential M).app (vtx o t) +
      M.map p ≫ middleSlot M t (𝟙 _) = middleSlot M i p := by
  induction p using path_induction' with
  | id =>
    erw [resolutionLift_id, Limits.zero_comp, zero_add, M.map_id, Category.id_comp]
  | comp p h ih =>
    have ih' := eq_sub_of_add_eq ih
    erw [resolutionLift_comp_gen]
    rw [Preadditive.add_comp, Category.assoc, (resolutionDifferential M).naturality,
      ← Category.assoc, ih', Category.assoc, leftSlot_resolutionDifferential_app,
      Preadditive.sub_comp, Category.assoc, middleSlot_map, middleSlot_map, Category.id_comp,
      Category.comp_id, M.map_comp]
    simp only [Preadditive.comp_sub, Category.assoc]
    abel

/-- The contracting map on all slots of the middle term at `t`. -/
noncomputable def resolutionRetraction (t : Fin (n + 1)) :
    (resolutionMiddle M).obj (vtx o t) ⟶ (resolutionLeft M).obj (vtx o t) :=
  sumDesc (fun i : Fin (n + 1) => i) (fun i => M.obj (vtx o i))
    fun i p => resolutionLift M i p

theorem middleSlot_resolutionRetraction (t : Fin (n + 1)) (i : Fin (n + 1))
    (p : vtx o i ⟶ vtx o t) :
    middleSlot M i p ≫ resolutionRetraction M t = resolutionLift M i p :=
  sumSlot_sumDesc (fun i : Fin (n + 1) => i) (fun i => M.obj (vtx o i)) _ i p

/-- The resolution splits at every vertex `t`: the retraction is `resolutionRetraction` and
the section is the main slot of `t`. -/
noncomputable def resolutionSplitting (t : Fin (n + 1)) :
    ((resolution M).map
      ((evaluation (Paths (Vertex o)) (ModuleCat.{u} k)).obj (vtx o t))).Splitting where
  r := resolutionRetraction M t
  s := middleSlot M t (𝟙 _)
  f_r := by
    change (resolutionDifferential M).app (vtx o t) ≫ resolutionRetraction M t = 𝟙 _
    refine left_hom_ext M fun e q => ?_
    rw [← Category.assoc, leftSlot_resolutionDifferential_app, Preadditive.sub_comp,
      Category.assoc, middleSlot_resolutionRetraction, middleSlot_resolutionRetraction,
      resolutionLift_differential, Category.comp_id]
  s_g := by
    change middleSlot M t (𝟙 _) ≫ (resolutionAugmentation M).app (vtx o t) = 𝟙 _
    rw [middleSlot_resolutionAugmentation_app, M.map_id]
  id := by
    change resolutionRetraction M t ≫ (resolutionDifferential M).app (vtx o t) +
      (resolutionAugmentation M).app (vtx o t) ≫ middleSlot M t (𝟙 _) = 𝟙 _
    refine middle_hom_ext M fun i p => ?_
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
      middleSlot_resolutionRetraction, middleSlot_resolutionAugmentation_app,
      resolutionLift_comp_differential, Category.comp_id]

/-- Pointwise exactness: at every vertex the standard resolution is a short exact sequence of
vector spaces. -/
theorem resolution_map_evaluation_shortExact (t : Paths (Vertex o)) :
    ((resolution M).map ((evaluation (Paths (Vertex o)) (ModuleCat.{u} k)).obj t)).ShortExact :=
  (resolutionSplitting M t).shortExact

/-- The standard resolution is a short exact sequence of diagrams. -/
theorem resolution_shortExact : (resolution M).ShortExact := by
  have hS := resolution_map_evaluation_shortExact M
  have : ∀ t, Mono ((resolution M).f.app t) := fun t => (hS t).mono_f
  have : ∀ t, Epi ((resolution M).g.app t) := fun t => (hS t).epi_g
  refine { exact := ?_, mono_f := NatTrans.mono_of_mono_app _, epi_g := NatTrans.epi_of_epi_app _ }
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun t => ?_
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp (hS t).exact)
    ((resolution M).mapHomologyIso ((evaluation (Paths (Vertex o)) (ModuleCat.{u} k)).obj t)).symm

/-- Diagrams have enough projectives: the augmentation of the standard resolution. -/
instance enoughProjectives_diagram : EnoughProjectives (Diagram k o) where
  presentation X :=
    ⟨{  p := resolutionMiddle X
        f := resolutionAugmentation X
        epi := (resolution_shortExact X).epi_g }⟩

/-- Every diagram has projective dimension at most one: the category of diagrams on an oriented
path is hereditary. -/
instance hasProjectiveDimensionLT_two : HasProjectiveDimensionLT M 2 := by
  have h₁ : HasProjectiveDimensionLT (resolution M).X₁ 1 := by
    change HasProjectiveDimensionLT (resolutionLeft M) 1
    infer_instance
  have h₂ : HasProjectiveDimensionLT (resolution M).X₂ 2 := by
    change HasProjectiveDimensionLT (resolutionMiddle M) 2
    exact hasProjectiveDimensionLT_of_ge _ 1 2 (by norm_num)
  exact (resolution_shortExact M).hasProjectiveDimensionLT_X₃ 1 h₁ h₂

/-- `Ext^m(M, N)` vanishes for `m ≥ 2`. -/
theorem ext_eq_zero [HasExt.{w} (Diagram k o)] (N : Diagram k o) {m : ℕ} (hm : 2 ≤ m)
    (e : Ext.{w} M N m) : e = 0 :=
  e.eq_zero_of_hasProjectiveDimensionLT 2 hm

/-- `Ext^m(M, N)` is a subsingleton for `m ≥ 2`. -/
theorem subsingleton_ext [HasExt.{w} (Diagram k o)] (N : Diagram k o) {m : ℕ} (hm : 2 ≤ m) :
    Subsingleton (Ext.{w} M N m) :=
  HasProjectiveDimensionLT.subsingleton M 2 m hm N

end TDA.Sheaf.AlternatingDiagram
