import TDA.Persistence.GeneratedUpsetResolution

/-!
# Functorial maps between generated-upset resolutions

Pointwise inequalities between indexed generators induce coefficient-preserving inclusions on
the existing occurrence-indexed face summands. Their biproducts form monomorphisms of the
existing augmented resolutions and commute with its signed deletion differential.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GeneratedUpsetResolutionMap

open CategoryTheory CategoryTheory.Limits
open TDA.Persistence.GeneratedUpsetResolution

variable {k : Type u} [Field k] {P : Type} [Lattice P]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

private theorem natural_map_structure {F G : PModule.{u,0,u} k P}
    (η : F ⟶ G) {a b : P} (hab : a ≤ b) (x : F.obj a) :
    (η.app b).hom (structureMapLinear F hab x) =
      structureMapLinear G hab ((η.app a).hom x) := by
  have hn := congrArg (fun φ : F.obj a ⟶ G.obj b => φ.hom x)
    (η.naturality (homOfLE hab))
  exact hn

private theorem structureMap_apply_comp (M : PModule.{u,0,u} k P)
    {a b c : P} (hab : a ≤ b) (hbc : b ≤ c) (x : M.obj a) :
    structureMapLinear M hbc (structureMapLinear M hab x) =
      structureMapLinear M (hab.trans hbc) x := by
  rw [← LinearMap.comp_apply, ← structureMapLinear_comp]

/-- The face birth for `g` lies below the corresponding face birth for `f` when `g ≤ f`. -/
theorem faceJoin_le_of_pointwise_le {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r : ℕ} (A : FaceIndex m r) :
    faceJoin g A ≤ faceJoin f A := by
  apply (faceJoin_le_iff g A (faceJoin f A)).mpr
  intro i hi
  exact (h i).trans (Finset.le_sup' (f := f) hi)

/-- The canonical coefficient-preserving inclusion on a corresponding pair of face summands. -/
noncomputable def faceMap {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r : ℕ} (A : FaceIndex m r) :
    faceModule (k := k) f A ⟶ faceModule (k := k) g A :=
  HookInfinity.fromBirth (faceJoin f A) (faceModule (k := k) g A)
    (structureMapLinear (faceModule (k := k) g A) (faceJoin_le_of_pointwise_le h A)
      (HookInfinity.birth (R := k) (faceJoin g A)))

/-- The face inclusion sends its birth generator to the target birth generator's structure image. -/
@[simp] theorem faceMap_birth {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r : ℕ} (A : FaceIndex m r) :
    ((faceMap (k := k) h A).app (faceJoin f A)).hom
        (HookInfinity.birth (R := k) (faceJoin f A)) =
      structureMapLinear (faceModule (k := k) g A) (faceJoin_le_of_pointwise_le h A)
        (HookInfinity.birth (R := k) (faceJoin g A)) :=
  HookInfinity.fromBirth_birth _ _ _

private theorem faceMap_basis {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r : ℕ} (A : FaceIndex m r) {p : P}
    (hf : faceJoin f A ≤ p) :
    ((faceMap (k := k) h A).app p).hom
        (structureMapLinear (faceModule (k := k) f A) hf
          (HookInfinity.birth (R := k) (faceJoin f A))) =
      structureMapLinear (faceModule (k := k) g A)
        ((faceJoin_le_of_pointwise_le h A).trans hf)
        (HookInfinity.birth (R := k) (faceJoin g A)) := by
  have hn := congrArg (fun φ : (faceModule (k := k) f A).obj (faceJoin f A) ⟶
      (faceModule (k := k) g A).obj p => φ.hom (HookInfinity.birth (R := k) (faceJoin f A)))
    ((faceMap (k := k) h A).naturality (homOfLE hf))
  change ((faceMap (k := k) h A).app p).hom
      (structureMapLinear (faceModule (k := k) f A) hf
        (HookInfinity.birth (R := k) (faceJoin f A))) =
    structureMapLinear (faceModule (k := k) g A) hf
      (((faceMap (k := k) h A).app (faceJoin f A)).hom
        (HookInfinity.birth (R := k) (faceJoin f A))) at hn
  calc
    _ = structureMapLinear (faceModule (k := k) g A) hf
        (structureMapLinear (faceModule (k := k) g A)
          (faceJoin_le_of_pointwise_le h A)
          (HookInfinity.birth (R := k) (faceJoin g A))) := by
          rw [hn, faceMap_birth]
    _ = structureMapLinear (faceModule (k := k) g A)
        ((faceJoin_le_of_pointwise_le h A).trans hf)
        (HookInfinity.birth (R := k) (faceJoin g A)) := by
          rw [← LinearMap.comp_apply, ← structureMapLinear_comp]

/-- On fibers where the source face exists, `faceMap` preserves its unique coefficient. -/
private theorem faceMap_fiberCoefficient {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r : ℕ} (A : FaceIndex m r) {p : P}
    (hf : faceJoin f A ≤ p) (x : (faceModule (k := k) f A).obj p) :
    HookInfinity.fiberEquivOfLe (R := k) ((faceJoin_le_of_pointwise_le h A).trans hf)
      (((faceMap (k := k) h A).app p).hom x) =
    HookInfinity.fiberEquivOfLe (R := k) hf x := by
  let eF := HookInfinity.fiberEquivOfLe (R := k) hf
  let eG := HookInfinity.fiberEquivOfLe (R := k)
    ((faceJoin_le_of_pointwise_le h A).trans hf)
  let x₀ := structureMapLinear (faceModule (k := k) f A) hf
    (HookInfinity.birth (R := k) (faceJoin f A))
  let y₀ := structureMapLinear (faceModule (k := k) g A)
    ((faceJoin_le_of_pointwise_le h A).trans hf)
    (HookInfinity.birth (R := k) (faceJoin g A))
  have hx₀ : eF x₀ = 1 := by
    rw [HookInfinity.fiberEquivOfLe_apply]
    change (structureMapLinear
      (GradedFree.module (R := k) (HookInfinity.generators (faceJoin f A))) hf
      (GradedFree.birth (R := k) (HookInfinity.generators (faceJoin f A)) ())).val () = 1
    have hval : (structureMapLinear
        (GradedFree.module (R := k) (HookInfinity.generators (faceJoin f A))) hf
        (GradedFree.birth (R := k) (HookInfinity.generators (faceJoin f A)) ())).val =
      (GradedFree.birth (R := k) (HookInfinity.generators (faceJoin f A)) ()).val := rfl
    rw [hval]
    simp [HookInfinity.generators, GradedFree.birth, GradedFree.generator]
  have hy₀ : eG y₀ = 1 := by
    rw [HookInfinity.fiberEquivOfLe_apply]
    change (structureMapLinear
      (GradedFree.module (R := k) (HookInfinity.generators (faceJoin g A)))
      ((faceJoin_le_of_pointwise_le h A).trans hf)
      (GradedFree.birth (R := k) (HookInfinity.generators (faceJoin g A)) ())).val () = 1
    have hval : (structureMapLinear
        (GradedFree.module (R := k) (HookInfinity.generators (faceJoin g A)))
        ((faceJoin_le_of_pointwise_le h A).trans hf)
        (GradedFree.birth (R := k) (HookInfinity.generators (faceJoin g A)) ())).val =
      (GradedFree.birth (R := k) (HookInfinity.generators (faceJoin g A)) ()).val := rfl
    rw [hval]
    simp [HookInfinity.generators, GradedFree.birth, GradedFree.generator]
  have hx : x = eF x • x₀ := by
    apply eF.injective
    simp [hx₀]
  conv_lhs => rw [hx]
  calc
    eG (((faceMap (k := k) h A).app p).hom (eF x • x₀)) =
        eG (eF x • ((faceMap (k := k) h A).app p).hom x₀) := by rw [map_smul]
    _ = eF x • eG (((faceMap (k := k) h A).app p).hom x₀) := by rw [map_smul]
    _ = eF x := by
      rw [faceMap_basis]
      have hy : eG (structureMapLinear (faceModule (k := k) g A)
          ((faceJoin_le_of_pointwise_le h A).trans hf)
          (HookInfinity.birth (R := k) (faceJoin g A))) = 1 := by
        simpa [y₀] using hy₀
      rw [hy]
      simp

/-- Every component of a principal-upset inclusion is injective. -/
theorem faceMap_app_injective {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r : ℕ} (A : FaceIndex m r) (p : P) :
    Function.Injective ((faceMap (k := k) h A).app p).hom := by
  intro x y hxy
  by_cases hf : faceJoin f A ≤ p
  · apply (HookInfinity.fiberEquivOfLe (R := k) hf).injective
    have hcoef := congrArg (HookInfinity.fiberEquivOfLe (R := k)
      ((faceJoin_le_of_pointwise_le h A).trans hf)) hxy
    rw [faceMap_fiberCoefficient (k := k) h A hf x,
      faceMap_fiberCoefficient (k := k) h A hf y] at hcoef
    exact hcoef
  · have hx := HookInfinity.fiber_eq_zero_of_not_le (R := k) hf x
    have hy := HookInfinity.fiber_eq_zero_of_not_le (R := k) hf y
    exact hx.trans hy.symm

/-- A principal-upset face inclusion is a categorical monomorphism. -/
theorem faceMap_mono {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r : ℕ} (A : FaceIndex m r) :
    Mono (faceMap (k := k) h A) := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro p
  exact (ModuleCat.mono_iff_injective _).2 (faceMap_app_injective (k := k) h A p)

/-- A principal-upset birth generator has coefficient one at every later index. -/
theorem principalBirth_coefficient {i p : P} (h : i ≤ p) :
    HookInfinity.fiberEquivOfLe (R := k) h
      (structureMapLinear (HookInfinity.module (R := k) i) h
        (HookInfinity.birth (R := k) i)) = 1 := by
  simpa [HookInfinity.fiberEquivOfLe_apply, HookInfinity.birth,
    HookInfinity.generators, GradedFree.birth, GradedFree.generator] using
      (HookInfinity.fiberEquivOfLe_structureMap (R := k)
        (le_rfl : i ≤ i) h (HookInfinity.birth (R := k) i))

/-- The face inclusion is the identity when the indexed generators are unchanged. -/
theorem faceMap_identity {m : ℕ} (f : Fin m → P) {r : ℕ} (A : FaceIndex m r) :
    faceMap (k := k) (fun _ => le_rfl) A = 𝟙 (faceModule (k := k) f A) := by
  apply HookInfinity.hom_ext
  simp [faceMap_birth, structureMapLinear_self]

/-- Corresponding face inclusions compose according to the pointwise order. -/
theorem faceMap_comp {m : ℕ} {f g v : Fin m → P}
    (hfg : ∀ i, g i ≤ f i) (hvg : ∀ i, v i ≤ g i) {r : ℕ}
    (A : FaceIndex m r) :
    faceMap (k := k) hfg A ≫ faceMap (k := k) hvg A =
      faceMap (k := k) (fun i => (hvg i).trans (hfg i)) A := by
  let hgf := faceJoin_le_of_pointwise_le hfg A
  let hvgA := faceJoin_le_of_pointwise_le hvg A
  let hvf := faceJoin_le_of_pointwise_le (fun i => (hvg i).trans (hfg i)) A
  apply HookInfinity.hom_ext
  apply (HookInfinity.fiberEquivOfLe (R := k) hvf).injective
  have hleft : HookInfinity.fiberEquivOfLe (R := k) hvf
      (((faceMap (k := k) hfg A ≫ faceMap (k := k) hvg A).app (faceJoin f A)).hom
        (HookInfinity.birth (R := k) (faceJoin f A))) = 1 := by
    have hfirst := faceMap_birth (k := k) hfg A
    have hsecond := faceMap_fiberCoefficient (k := k) hvg A hgf
      (structureMapLinear (faceModule (k := k) g A) hgf
        (HookInfinity.birth (R := k) (faceJoin g A)))
    have hcoeff : HookInfinity.fiberEquivOfLe (R := k) hgf
        (structureMapLinear (faceModule (k := k) g A) hgf
          (HookInfinity.birth (R := k) (faceJoin g A))) = 1 := by
      simpa using principalBirth_coefficient (k := k) hgf
    rw [NatTrans.comp_app, ModuleCat.comp_apply, hfirst]
    simpa [hgf, hvf, hvgA, hsecond] using hcoeff
  have hright : HookInfinity.fiberEquivOfLe (R := k) hvf
      (((faceMap (k := k) (fun i => (hvg i).trans (hfg i)) A).app
        (faceJoin f A)).hom (HookInfinity.birth (R := k) (faceJoin f A))) = 1 := by
    rw [faceMap_birth]
    simpa [hvf] using principalBirth_coefficient (k := k) hvf
  rw [hleft, hright]

/-- The face maps commute with every existing face inclusion. -/
private theorem faceMap_inclusion_square {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {r s : ℕ} (A : FaceIndex m r) (B : FaceIndex m s)
    (hBA : B.1 ⊆ A.1) :
    faceMap (k := k) h A ≫ inclusion (k := k) g A B hBA =
      inclusion (k := k) f A B hBA ≫ faceMap (k := k) h B := by
  let hgfA := faceJoin_le_of_pointwise_le h A
  let hgfB := faceJoin_le_of_pointwise_le h B
  let hfBA := faceJoin_mono f A B hBA
  let hgBA := faceJoin_mono g A B hBA
  let hleft := hgfB.trans hfBA
  let hright := hgBA.trans hgfA
  apply HookInfinity.hom_ext
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  rw [faceMap_birth]
  calc
    ((inclusion (k := k) g A B hBA).app (faceJoin f A)).hom
        (structureMapLinear (faceModule (k := k) g A) hgfA
          (HookInfinity.birth (R := k) (faceJoin g A))) =
      structureMapLinear (faceModule (k := k) g B) hgfA
        (((inclusion (k := k) g A B hBA).app (faceJoin g A)).hom
          (HookInfinity.birth (R := k) (faceJoin g A))) := by
            exact natural_map_structure (inclusion (k := k) g A B hBA) hgfA _
    _ = structureMapLinear (faceModule (k := k) g B) hgfA
        (structureMapLinear (faceModule (k := k) g B) hgBA
          (HookInfinity.birth (R := k) (faceJoin g B))) := by rw [inclusion_birth]
    _ = structureMapLinear (faceModule (k := k) g B) hleft
        (HookInfinity.birth (R := k) (faceJoin g B)) := by
          rw [structureMap_apply_comp]
    _ = structureMapLinear (faceModule (k := k) g B) hright
        (HookInfinity.birth (R := k) (faceJoin g B)) := by
          rfl
    _ = structureMapLinear (faceModule (k := k) g B) hfBA
        (((faceMap (k := k) h B).app (faceJoin f B)).hom
          (HookInfinity.birth (R := k) (faceJoin f B))) := by
            rw [faceMap_birth, structureMap_apply_comp]
    _ = ((faceMap (k := k) h B).app (faceJoin f A)).hom
        (structureMapLinear (faceModule (k := k) f B) hfBA
          (HookInfinity.birth (R := k) (faceJoin f B))) := by
            symm
            exact natural_map_structure (faceMap (k := k) h B) hfBA _
    _ = ((faceMap (k := k) h B).app (faceJoin f A)).hom
        (((inclusion (k := k) f A B hBA).app (faceJoin f A)).hom
          (HookInfinity.birth (R := k) (faceJoin f A))) := by rw [inclusion_birth]

/-- The face maps commute with each signed deletion map. -/
private theorem faceMap_signedDeletionAt {m r : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (A : FaceIndex m (r + 1)) (j : Fin (r + 2)) :
    faceMap (k := k) h A ≫ signedDeletionAt (k := k) g A j =
      signedDeletionAt (k := k) f A j ≫
        faceMap (k := k) h (eraseFaceAt A j) := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [signedDeletionAt, scalarMultiple, NatTrans.comp_app, ModuleCat.comp_apply]
  have hsquare := congrArg (fun φ : faceModule (k := k) f A ⟶
      faceModule (k := k) g (eraseFaceAt A j) => (φ.app p).hom x)
    (faceMap_inclusion_square (k := k) h A (eraseFaceAt A j)
      (eraseFaceAt_subset A j))
  change ((-1 : k) ^ (j : ℕ) •
      ((inclusion (k := k) g A (eraseFaceAt A j) (eraseFaceAt_subset A j)).app p).hom)
      (((faceMap (k := k) h A).app p).hom x) =
    ((faceMap (k := k) h (eraseFaceAt A j)).app p).hom
      (((-1 : k) ^ (j : ℕ) •
        ((inclusion (k := k) f A (eraseFaceAt A j) (eraseFaceAt_subset A j)).app p).hom) x)
  conv_rhs => rw [LinearMap.smul_apply]
  rw [map_smul]
  exact congrArg (fun y => (-1 : k) ^ (j : ℕ) • y) hsquare

/-- The degree-`r` map is the biproduct of corresponding face inclusions. -/
noncomputable def resolutionMap {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (r : ℕ) :
    term (k := k) f r ⟶ term (k := k) g r := by
  classical
  let F : FaceIndex m r → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) f A
  let G : FaceIndex m r → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) g A
  letI : HasBiproduct F := inferInstance
  letI : HasBiproduct G := inferInstance
  exact biproduct.map (fun A => faceMap (k := k) h A)

/-- The degree map acts on each existing face summand by its canonical inclusion. -/
@[reassoc (attr := simp)] theorem resolutionMap_ι {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (r : ℕ) (A : FaceIndex m r) :
    biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A ≫
        resolutionMap (k := k) h r =
      faceMap (k := k) h A ≫
        biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B) A := by
  classical
  exact biproduct.ι_map (fun A => faceMap (k := k) h A) A

/-- The resolution map sends a face birth generator to its target face structure image. -/
@[simp] theorem resolutionMap_faceBirth {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (r : ℕ) (A : FaceIndex m r) :
    ((resolutionMap (k := k) h r).app (faceJoin f A)).hom
        ((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A).app
          (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A))) =
      (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B) A).app
        (faceJoin f A)
        (structureMapLinear (faceModule (k := k) g A) (faceJoin_le_of_pointwise_le h A)
          (HookInfinity.birth (R := k) (faceJoin g A))) := by
  have he := congrArg (fun φ : faceModule (k := k) f A ⟶ term (k := k) g r =>
      (φ.app (faceJoin f A)).hom (HookInfinity.birth (R := k) (faceJoin f A)))
    (resolutionMap_ι (k := k) h r A)
  simpa only [NatTrans.comp_app, ModuleCat.comp_apply, faceMap_birth] using he

/-- The degreewise map is a categorical monomorphism. -/
theorem resolutionMap_mono {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (r : ℕ) : Mono (resolutionMap (k := k) h r) := by
  classical
  let F : FaceIndex m r → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) f A
  let G : FaceIndex m r → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) g A
  letI : HasBiproduct F := inferInstance
  letI : HasBiproduct G := inferInstance
  letI : ∀ A : FaceIndex m r, Mono (faceMap (k := k) (r := r) h A) :=
    fun A => faceMap_mono (k := k) (r := r) h A
  change Mono (biproduct.map (fun A => faceMap (k := k) h A))
  infer_instance

/-- Every fiber map of the resolution monomorphism is injective. -/
theorem resolutionMap_app_injective {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (r : ℕ) (p : P) :
    Function.Injective ((resolutionMap (k := k) h r).app p).hom := by
  exact (ModuleCat.mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app _).mp (resolutionMap_mono (k := k) h r) p)

/-- Equal indexed generators induce the identity on each resolution term. -/
theorem resolutionMap_identity {m : ℕ} (f : Fin m → P) (r : ℕ) :
    resolutionMap (k := k) (fun _ => le_rfl) r = 𝟙 (term (k := k) f r) := by
  classical
  apply biproduct.hom_ext'
  intro A
  rw [resolutionMap_ι, faceMap_identity]
  simp

/-- Degreewise resolution maps respect composition of pointwise inequalities. -/
theorem resolutionMap_comp {m : ℕ} {f g v : Fin m → P}
    (hfg : ∀ i, g i ≤ f i) (hvg : ∀ i, v i ≤ g i) (r : ℕ) :
    resolutionMap (k := k) hfg r ≫ resolutionMap (k := k) hvg r =
      resolutionMap (k := k) (fun i => (hvg i).trans (hfg i)) r := by
  classical
  apply biproduct.hom_ext'
  intro A
  calc
    _ = (faceMap (k := k) hfg A ≫
        biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B) A) ≫
          resolutionMap (k := k) hvg r := by
            rw [← Category.assoc, resolutionMap_ι, Category.assoc]
    _ = faceMap (k := k) hfg A ≫
        (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B) A ≫
          resolutionMap (k := k) hvg r) := by rw [Category.assoc]
    _ = faceMap (k := k) hfg A ≫
        (faceMap (k := k) hvg A ≫
          biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) v B) A) := by
          rw [resolutionMap_ι]
    _ = (faceMap (k := k) hfg A ≫ faceMap (k := k) hvg A) ≫
        biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) v B) A := by
          rw [← Category.assoc]
    _ = faceMap (k := k) (fun i => (hvg i).trans (hfg i)) A ≫
        biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) v B) A := by
          rw [faceMap_comp]
    _ = biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A ≫
        resolutionMap (k := k) (fun i => (hvg i).trans (hfg i)) r := by
          rw [← resolutionMap_ι]

/-- The resolution maps commute with the actual signed deletion differentials. -/
theorem resolutionMap_differential {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (r : ℕ) :
    resolutionMap (k := k) h (r + 1) ≫ differential (k := k) g r =
      differential (k := k) f r ≫ resolutionMap (k := k) h r := by
  classical
  apply biproduct.hom_ext'
  intro A
  calc
    _ = (faceMap (k := k) h A ≫
        biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) g B) A) ≫
          differential (k := k) g r := by
            rw [← Category.assoc, resolutionMap_ι, Category.assoc]
    _ = faceMap (k := k) h A ≫
        (biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) g B) A ≫
          differential (k := k) g r) := by rw [Category.assoc]
    _ = faceMap (k := k) h A ≫
        (∑ j : Fin (r + 2), signedDeletionAt (k := k) g A j ≫
          biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B)
            (eraseFaceAt A j)) := by rw [differential_ι]
    _ = ∑ j : Fin (r + 2), faceMap (k := k) h A ≫
          (signedDeletionAt (k := k) g A j ≫
            biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B)
              (eraseFaceAt A j)) := by rw [Preadditive.comp_sum]
    _ = ∑ j : Fin (r + 2),
          (signedDeletionAt (k := k) f A j ≫
            faceMap (k := k) h (eraseFaceAt A j)) ≫
            biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B)
              (eraseFaceAt A j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Category.assoc, faceMap_signedDeletionAt, Category.assoc]
    _ = ∑ j : Fin (r + 2), signedDeletionAt (k := k) f A j ≫
          (faceMap (k := k) h (eraseFaceAt A j) ≫
            biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) g B)
              (eraseFaceAt A j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Category.assoc]
    _ = ∑ j : Fin (r + 2), signedDeletionAt (k := k) f A j ≫
          (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B)
              (eraseFaceAt A j) ≫ resolutionMap (k := k) h r) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← resolutionMap_ι]
    _ = (∑ j : Fin (r + 2), signedDeletionAt (k := k) f A j ≫
          biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B)
            (eraseFaceAt A j)) ≫ resolutionMap (k := k) h r := by
        rw [Preadditive.sum_comp]
        simp only [Category.assoc]
    _ = (biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) f B) A ≫
          differential (k := k) f r) ≫ resolutionMap (k := k) h r := by
        rw [← differential_ι]
    _ = biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) f B) A ≫
          (differential (k := k) f r ≫ resolutionMap (k := k) h r) := by
        rw [Category.assoc]

/-- Pointwise generator inequalities induce inclusion of the generated upper supports. -/
theorem generatedSupport_mono {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) : generatedSupport f ⊆ generatedSupport g := by
  rintro p ⟨i, hi⟩
  exact ⟨i, (h i).trans hi⟩

private theorem generatedSupport_comparison_compat {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) :
    ∀ p q, p ≤ q → p ∈ generatedSupport f → q ∈ generatedSupport g →
      (q ∈ generatedSupport f ↔ p ∈ generatedSupport g) := by
  intro p q hpq hp _
  constructor
  · intro _
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, (h i).trans hi⟩
  · intro _
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, hi.trans hpq⟩

/-- The coefficient-preserving inclusion between the two generated-support modules. -/
noncomputable def supportMap {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) :
    SupportInterval.module (k := k) (generatedSupport f)
        (generatedSupport_ordConnected f) ⟶
      SupportInterval.module (k := k) (generatedSupport g)
        (generatedSupport_ordConnected g) :=
  SupportInterval.comparison (k := k) (generatedSupport f) (generatedSupport g)
    (generatedSupport_ordConnected f) (generatedSupport_ordConnected g) 1
    (generatedSupport_comparison_compat h)

/-- On the source support, the canonical support map preserves the scalar. -/
theorem supportMap_app_val {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) {p : P} (hp : p ∈ generatedSupport f)
    (x : SupportInterval.fiber (k := k) (generatedSupport f) p) :
    (((supportMap (k := k) h).app p).hom x : k) = (x : k) := by
  rw [supportMap, SupportInterval.comparison_app_val]
  have hgp : p ∈ generatedSupport g := generatedSupport_mono h hp
  simp [hgp]

/-- Every fiber map of the generated-support inclusion is injective. -/
theorem supportMap_app_injective {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (p : P) :
    Function.Injective ((supportMap (k := k) h).app p).hom := by
  intro x y hxy
  by_cases hp : p ∈ generatedSupport f
  · apply Subtype.ext
    have hx := supportMap_app_val (k := k) h hp x
    have hy := supportMap_app_val (k := k) h hp y
    calc
      (x : k) = (((supportMap (k := k) h).app p).hom x : k) := hx.symm
      _ = (((supportMap (k := k) h).app p).hom y : k) := congrArg Subtype.val hxy
      _ = (y : k) := hy
  · apply Subtype.ext
    rw [SupportInterval.val_eq_zero (k := k) (generatedSupport f) hp x,
      SupportInterval.val_eq_zero (k := k) (generatedSupport f) hp y]

/-- The generated-support inclusion is a categorical monomorphism. -/
theorem supportMap_mono {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) : Mono (supportMap (k := k) h) := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro p
  exact (ModuleCat.mono_iff_injective _).2 (supportMap_app_injective (k := k) h p)

/-- Face augmentations commute with the coefficient-preserving support inclusion. -/
theorem augmentationComponent_square {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) (A : FaceIndex m 0) :
    faceMap (k := k) h A ≫ augmentationComponent (k := k) g A =
      augmentationComponent (k := k) f A ≫ supportMap (k := k) h := by
  apply HookInfinity.hom_ext
  apply Subtype.ext
  let p := faceJoin f A
  have hpF : p ∈ generatedSupport f := by
    exact faceJoin_mem_support f A
  have hpG : p ∈ generatedSupport g := generatedSupport_mono h hpF
  have hbirth : faceJoin g A ≤ p := by
    dsimp [p]
    exact faceJoin_le_of_pointwise_le h A
  have hleft := augmentationComponent_val (k := k) g A hbirth hpG
  have hright := augmentationComponent_val (k := k) f A (le_rfl) hpF
  change (((augmentationComponent (k := k) g A).app p).hom
      (((faceMap (k := k) h A).app p).hom
        (HookInfinity.birth (R := k) (faceJoin f A))) : k) =
    (((supportMap (k := k) h).app p).hom
      (((augmentationComponent (k := k) f A).app p).hom
        (HookInfinity.birth (R := k) (faceJoin f A))) : k)
  rw [faceMap_birth]
  rw [supportMap_app_val (k := k) h hpF]
  exact hleft.trans hright.symm

/-- The augmented degree-zero resolution map commutes with its actual augmentation. -/
theorem resolutionMap_augmentation {m : ℕ} {f g : Fin m → P}
    (h : ∀ i, g i ≤ f i) :
    resolutionMap (k := k) h 0 ≫ augmentation (k := k) g =
      augmentation (k := k) f ≫ supportMap (k := k) h := by
  classical
  apply biproduct.hom_ext'
  intro A
  calc
    _ = (faceMap (k := k) h A ≫
        biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) g B) A) ≫
          augmentation (k := k) g := by
            rw [← Category.assoc, resolutionMap_ι, Category.assoc]
    _ = faceMap (k := k) h A ≫
        (biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) g B) A ≫
          augmentation (k := k) g) := by rw [Category.assoc]
    _ = faceMap (k := k) h A ≫ augmentationComponent (k := k) g A := by
          rw [augmentation_ι]
    _ = augmentationComponent (k := k) f A ≫ supportMap (k := k) h := by
          rw [augmentationComponent_square]
    _ = (biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A ≫
          augmentation (k := k) f) ≫ supportMap (k := k) h := by
            rw [← augmentation_ι]
    _ = biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A ≫
          (augmentation (k := k) f ≫ supportMap (k := k) h) := by
            rw [Category.assoc]

end TDA.Persistence.GeneratedUpsetResolutionMap
