import TDA.Persistence.HookInfinity
import TDA.Persistence.HookInfinityProjective
import TDA.Persistence.SupportInterval
import TDA.Simplicial.Cone
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort

/-!
# Projective resolutions of finitely generated upsets

For a finite indexed family in a lattice, this file constructs the alternating join-indexed
resolution of the support module of its generated upset. The indices are subsets of occurrences,
so equal generators remain distinct. Exactness is checked at each lattice element by identifying
the active summands with the augmented simplex on the active occurrences.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.GeneratedUpsetResolution

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [Lattice P]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The finite set indexing degree-`r` summands. -/
abbrev FaceIndex (m r : ℕ) := {A : Finset (Fin m) // A.card = r + 1}

/-- Every degree index is a nonempty set of generator occurrences. -/
theorem face_nonempty {m r : ℕ} (A : FaceIndex m r) : A.1.Nonempty := by
  apply Finset.card_pos.mp
  rw [A.2]
  omega

/-- The join of the generator occurrences indexed by a nonempty face. -/
noncomputable def faceJoin {m : ℕ} (f : Fin m → P) {r : ℕ} (A : FaceIndex m r) : P :=
  A.1.sup' (face_nonempty A) f

/-- The principal-upset module born at a face join. -/
noncomputable abbrev faceModule {m : ℕ} (f : Fin m → P) {r : ℕ}
    (A : FaceIndex m r) : PModule.{u,0,u} k P :=
  HookInfinity.module (R := k) (faceJoin f A)

/-- Inclusion of faces reverses the direction of their principal-upset modules. -/
theorem faceJoin_mono {m : ℕ} (f : Fin m → P) {r s : ℕ}
    (A : FaceIndex m r) (B : FaceIndex m s) (hBA : B.1 ⊆ A.1) :
    faceJoin f B ≤ faceJoin f A := by
  exact Finset.sup'_mono f hBA (face_nonempty B)

/-- A face join lies below a point exactly when each selected generator does. -/
theorem faceJoin_le_iff {m : ℕ} (f : Fin m → P) {r : ℕ}
    (A : FaceIndex m r) (p : P) :
    faceJoin f A ≤ p ↔ ∀ i ∈ A.1, f i ≤ p := by
  change A.1.sup' (face_nonempty A) f ≤ p ↔ ∀ i ∈ A.1, f i ≤ p
  simpa only using (Finset.sup'_le_iff (s := A.1) (H := face_nonempty A)
    (f := f) (a := p))

/-- The canonical map from the later-born principal upset to the earlier-born one. -/
noncomputable def inclusion {m : ℕ} (f : Fin m → P) {r s : ℕ}
    (A : FaceIndex m r) (B : FaceIndex m s) (hBA : B.1 ⊆ A.1) :
    faceModule (k := k) f A ⟶ faceModule (k := k) f B :=
  HookInfinity.fromBirth (faceJoin f A) (faceModule (k := k) f B)
    (structureMapLinear (faceModule (k := k) f B) (faceJoin_mono f A B hBA)
      (HookInfinity.birth (R := k) (faceJoin f B)))

/-- Inclusion maps preserve the distinguished generator at the larger birth. -/
@[simp] theorem inclusion_birth {m : ℕ} (f : Fin m → P) {r s : ℕ}
    (A : FaceIndex m r) (B : FaceIndex m s) (hBA : B.1 ⊆ A.1) :
    ((inclusion (k := k) f A B hBA).app (faceJoin f A)).hom
      (HookInfinity.birth (R := k) (faceJoin f A)) =
        structureMapLinear (faceModule (k := k) f B) (faceJoin_mono f A B hBA)
          (HookInfinity.birth (R := k) (faceJoin f B)) := by
  exact HookInfinity.fromBirth_birth _ _ _

/-- The degree-`r` term is the finite biproduct over faces with `r+1` occurrences. -/
noncomputable abbrev term {m : ℕ} (f : Fin m → P) (r : ℕ) : PModule.{u,0,u} k P := by
  classical
  exact ⨁ (fun A : FaceIndex m r => faceModule (k := k) f A)

/-- The graded-free family whose generators are the faces in one degree. -/
noncomputable abbrev faceGenerators {m : ℕ} (f : Fin m → P) (r : ℕ) :
    GradedFree.GradedGenerators.{0,0} P where
  Carrier := FaceIndex m r
  grade := faceJoin f

/-- The same face sum represented as a graded-free module. -/
noncomputable abbrev freeTerm {m : ℕ} (f : Fin m → P) (r : ℕ) : PModule.{u,0,u} k P :=
  GradedFree.module (R := k) (faceGenerators f r)

/-- Include the graded-free face sum into the finite categorical biproduct. -/
noncomputable def freeToTerm {m : ℕ} (f : Fin m → P) (r : ℕ) :
    freeTerm (k := k) f r ⟶ term (k := k) f r := by
  classical
  let F : FaceIndex m r → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) f A
  letI : HasBiproduct F := inferInstance
  exact GradedFree.lift (faceGenerators f r) (term (k := k) f r)
    (fun A => (biproduct.ι F A).app (faceJoin f A)
      (HookInfinity.birth (R := k) (faceJoin f A)))

/-- The free generator at a face maps to that face's biproduct injection. -/
@[simp] theorem freeToTerm_birth {m : ℕ} (f : Fin m → P) (r : ℕ)
    (A : FaceIndex m r) :
    (freeToTerm (k := k) f r).app (faceJoin f A)
      (GradedFree.birth (R := k) (faceGenerators f r) A) =
    (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A).app
      (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A)) :=
  GradedFree.lift_birth (faceGenerators f r) (term (k := k) f r)
    (fun B => (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) B).app
      (faceJoin f B) (HookInfinity.birth (R := k) (faceJoin f B))) A

/-- Project the finite categorical biproduct onto its graded-free face sum. -/
noncomputable def termToFree {m : ℕ} (f : Fin m → P) (r : ℕ) :
    term (k := k) f r ⟶ freeTerm (k := k) f r := by
  classical
  exact biproduct.desc (fun A : FaceIndex m r => HookInfinity.fromBirth (faceJoin f A)
    (freeTerm (k := k) f r) (GradedFree.birth (R := k) (faceGenerators f r) A))

/-- The map from one face summand into its graded-free counterpart is the chosen inclusion. -/
@[simp] theorem termToFree_ι {m : ℕ} (f : Fin m → P) (r : ℕ)
    (A : FaceIndex m r) :
    biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A ≫
      termToFree (k := k) f r =
    HookInfinity.fromBirth (faceJoin f A) (freeTerm (k := k) f r)
      (GradedFree.birth (R := k) (faceGenerators f r) A) := by
  classical
  dsimp only [termToFree]
  rw [biproduct.ι_desc]

/-- The finite biproduct and graded-free representations of a face sum agree. -/
noncomputable def termBiproductIso {m : ℕ} (f : Fin m → P) (r : ℕ) :
    term (k := k) f r ≅ freeTerm (k := k) f r where
  hom := termToFree (k := k) f r
  inv := freeToTerm (k := k) f r
  hom_inv_id := by
    classical
    apply biproduct.hom_ext'
    intro A
    apply HookInfinity.hom_ext
    change (((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A ≫
      (termToFree (k := k) f r ≫ freeToTerm (k := k) f r)).app (faceJoin f A)).hom
        (HookInfinity.birth (R := k) (faceJoin f A))) =
      ((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A).app
        (faceJoin f A)).hom (HookInfinity.birth (R := k) (faceJoin f A))
    rw [← Category.assoc, termToFree_ι]
    change (freeToTerm (k := k) f r).app (faceJoin f A)
        ((HookInfinity.fromBirth (faceJoin f A) (freeTerm (k := k) f r)
          (GradedFree.birth (R := k) (faceGenerators f r) A)).app (faceJoin f A)
          (HookInfinity.birth (R := k) (faceJoin f A))) = _
    rw [HookInfinity.fromBirth_birth]
    exact freeToTerm_birth (k := k) f r A
  inv_hom_id := by
    classical
    let s : ∀ A : FaceIndex m r,
        (freeTerm (k := k) f r).obj (faceJoin f A) :=
      fun A => GradedFree.birth (R := k) (faceGenerators f r) A
    have hcomp := GradedFree.lift_unique (faceGenerators f r) (freeTerm (k := k) f r)
      s (freeToTerm (k := k) f r ≫ termToFree (k := k) f r) (by
        intro A
        change (termToFree (k := k) f r).app (faceJoin f A)
          ((freeToTerm (k := k) f r).app (faceJoin f A)
            (GradedFree.birth (R := k) (faceGenerators f r) A)) = s A
        rw [freeToTerm_birth]
        have hι := termToFree_ι (k := k) f r A
        have hh := congrArg (fun α => α.app (faceJoin f A)) hι
        have hv := congrArg (fun g => g
          (HookInfinity.birth (R := k) (faceJoin f A))) hh
        simpa only [NatTrans.comp_app, ModuleCat.comp_apply, HookInfinity.fromBirth_birth, s]
          using hv)
    have hid := GradedFree.lift_unique (faceGenerators f r) (freeTerm (k := k) f r)
      s (𝟙 (freeTerm (k := k) f r)) (by
        intro A
        simp [s])
    exact hcomp.trans hid.symm

/-- Deprecated compatibility name for principal-upset projectivity. -/
@[deprecated TDA.Persistence.HookInfinity.projective (since := "2026-10-30")]
theorem HookInfinity.projective (i : P) :
    Projective (HookInfinity.module (R := k) i) :=
  TDA.Persistence.HookInfinity.projective i

/-- Every term in the finite join-indexed sequence is ordinary projective. -/
theorem term_projective {m : ℕ} (f : Fin m → P) (r : ℕ) : Projective (term (k := k) f r) := by
  classical
  let F : FaceIndex m r → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) f A
  have hF : ∀ A, Projective (F A) := fun A => by
    change Projective (HookInfinity.module (R := k) (faceJoin f A))
    infer_instance
  change Projective (⨁ F)
  letI : HasBiproduct F := inferInstance
  constructor
  intro E X α e he
  letI : Epi e := he
  choose β hβ using fun A => (hF A).factors (biproduct.ι F A ≫ α) e
  refine ⟨biproduct.desc β, ?_⟩
  apply biproduct.hom_ext'
  intro A
  rw [← Category.assoc, biproduct.ι_desc]
  exact hβ A

/-- Erase one occurrence from a face, lowering its cardinality by one. -/
def eraseFace {m r : ℕ} (A : FaceIndex m (r + 1)) (i : Fin m) (hi : i ∈ A.1) :
    FaceIndex m r := by
  refine ⟨A.1.erase i, ?_⟩
  rw [Finset.card_erase_of_mem hi, A.2]
  omega

/-- The position of an occurrence in the increasing order on a face. -/
def deletionPosition {m r : ℕ} (A : FaceIndex m (r + 1)) (i : Fin m) : ℕ :=
  (A.1.filter (· < i)).card

/-- Multiplication of every component of a natural transformation by a scalar. -/
noncomputable def scalarMultiple {M N : PModule.{u,0,u} k P} (c : k) (α : M ⟶ N) : M ⟶ N where
  app p := ModuleCat.ofHom (c • (α.app p).hom)
  naturality {p q} h := by
    have hn := congrArg (fun g => g.hom) (α.naturality h)
    apply ModuleCat.hom_ext
    change (c • (α.app q).hom).comp (M.map h).hom =
      (N.map h).hom.comp (c • (α.app p).hom)
    rw [LinearMap.smul_comp, LinearMap.comp_smul]
    exact congrArg (fun g => c • g) hn

/-- The signed canonical inclusion associated to deleting one occurrence. -/
noncomputable def signedDeletion {m r : ℕ} (f : Fin m → P)
    (A : FaceIndex m (r + 1)) (i : Fin m) (hi : i ∈ A.1) :
    faceModule (k := k) f A ⟶ faceModule (k := k) f (eraseFace A i hi) :=
  scalarMultiple ((-1 : k) ^ deletionPosition A i)
    (inclusion (k := k) f A (eraseFace A i hi) (Finset.erase_subset _ _))

/-- The occurrence in position `j` in the increasing enumeration of a face. -/
def faceOccurrence {m r : ℕ} (A : FaceIndex m (r + 1)) (j : Fin (r + 2)) : Fin m :=
  A.1.orderEmbOfFin A.2 j

/-- Delete the occurrence at ordered position `j`. -/
def eraseFaceAt {m r : ℕ} (A : FaceIndex m (r + 1)) (j : Fin (r + 2)) :
    FaceIndex m r := by
  let i := faceOccurrence A j
  have hi : i ∈ A.1 := Finset.orderEmbOfFin_mem A.1 A.2 j
  refine ⟨A.1.erase i, ?_⟩
  rw [Finset.card_erase_of_mem hi, A.2]
  omega

/-- The ordered face obtained by deletion is a subset of its source face. -/
theorem eraseFaceAt_subset {m r : ℕ} (A : FaceIndex m (r + 1))
    (j : Fin (r + 2)) : (eraseFaceAt A j).1 ⊆ A.1 := by
  change A.1.erase (faceOccurrence A j) ⊆ A.1
  exact Finset.erase_subset _ _

/-- The signed canonical inclusion at ordered position `j`. -/
noncomputable def signedDeletionAt {m r : ℕ} (f : Fin m → P)
    (A : FaceIndex m (r + 1)) (j : Fin (r + 2)) :
    faceModule (k := k) f A ⟶ faceModule (k := k) f (eraseFaceAt A j) :=
  scalarMultiple ((-1 : k) ^ (j : ℕ))
    (inclusion (k := k) f A (eraseFaceAt A j) (eraseFaceAt_subset A j))

/-- A signed face inclusion sends the source birth to the signed target birth image. -/
@[simp] theorem signedDeletionAt_birth {m r : ℕ} (f : Fin m → P)
    (A : FaceIndex m (r + 1)) (j : Fin (r + 2)) :
    (signedDeletionAt (k := k) f A j).app (faceJoin f A)
        (HookInfinity.birth (R := k) (faceJoin f A)) =
      (-1 : k) ^ (j : ℕ) • structureMapLinear
        (faceModule (k := k) f (eraseFaceAt A j))
            (faceJoin_mono f A (eraseFaceAt A j) (eraseFaceAt_subset A j))
        (HookInfinity.birth (R := k) (faceJoin f (eraseFaceAt A j))) := by
  change (-1 : k) ^ (j : ℕ) •
    ((inclusion (k := k) f A (eraseFaceAt A j) (Finset.erase_subset _ _)).app
      (faceJoin f A)).hom (HookInfinity.birth (R := k) (faceJoin f A)) = _
  simp [inclusion, HookInfinity.fromBirth_birth]

/-- The signed alternating deletion differential between consecutive terms. -/
noncomputable def differential {m : ℕ} (f : Fin m → P) (r : ℕ) :
    term (k := k) f (r + 1) ⟶ term (k := k) f r := by
  classical
  let F : FaceIndex m (r + 1) → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) f A
  let G : FaceIndex m r → PModule.{u,0,u} k P :=
    fun B => faceModule (k := k) f B
  letI : HasBiproduct F := inferInstance
  letI : HasBiproduct G := inferInstance
  exact biproduct.desc (fun A =>
    ∑ j : Fin (r + 2), signedDeletionAt (k := k) f A j ≫
      biproduct.ι G (eraseFaceAt A j))

/-- On one source summand, the differential is the alternating sum of its deletions. -/
theorem differential_ι {m : ℕ} (f : Fin m → P) (r : ℕ)
    (A : FaceIndex m (r + 1)) :
    biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) f B) A ≫
        differential (k := k) f r =
      ∑ j : Fin (r + 2), signedDeletionAt (k := k) f A j ≫
        biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B)
          (eraseFaceAt A j) := by
  classical
  rw [differential, biproduct.ι_desc]

/-- The upper set generated by an indexed family, retaining repeated occurrences. -/
def generatedSupport {m : ℕ} (f : Fin m → P) : Set P :=
  {p | ∃ i, f i ≤ p}

/-- A generated upper set is order convex. -/
theorem generatedSupport_ordConnected {m : ℕ} (f : Fin m → P) :
    (generatedSupport f).OrdConnected := by
  rw [Set.ordConnected_def]
  intro p hp q hq x hx
  obtain ⟨i, hi⟩ := hp
  exact ⟨i, hi.trans hx.1⟩

/-- Every nonempty face join belongs to the generated support. -/
theorem faceJoin_mem_support {m : ℕ} (f : Fin m → P) {r : ℕ}
    (A : FaceIndex m r) : faceJoin f A ∈ generatedSupport f := by
  obtain ⟨i, hi⟩ := (face_nonempty A).exists_mem
  exact ⟨i, Finset.le_sup' (f := f) hi⟩

/-- The augmentation component from a face hook to the support module. -/
noncomputable def augmentationComponent {m : ℕ} (f : Fin m → P)
    (A : FaceIndex m 0) : faceModule (k := k) f A ⟶
      SupportInterval.module (generatedSupport f) (generatedSupport_ordConnected f) := by
  let j := faceJoin f A
  exact HookInfinity.fromBirth j _
    (SupportInterval.one (k := k) (generatedSupport f) (faceJoin_mem_support f A))

/-- The augmentation to the module supported on the generated upset. -/
noncomputable def augmentation {m : ℕ} (f : Fin m → P) :
    term (k := k) f 0 ⟶
      SupportInterval.module (generatedSupport f) (generatedSupport_ordConnected f) := by
  classical
  let F : FaceIndex m 0 → PModule.{u,0,u} k P :=
    fun A => faceModule (k := k) f A
  letI : HasBiproduct F := inferInstance
  exact biproduct.desc (fun A => augmentationComponent (k := k) f A)

/-- On a degree-zero face summand, the augmentation is its canonical hook map. -/
theorem augmentation_ι {m : ℕ} (f : Fin m → P) (A : FaceIndex m 0) :
    biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A ≫
        augmentation (k := k) f = augmentationComponent (k := k) f A := by
  classical
  rw [augmentation, biproduct.ι_desc]

/-- A face-hook augmentation sends its birth generator to the support unit. -/
theorem augmentationComponent_val {m : ℕ} (f : Fin m → P) (A : FaceIndex m 0)
    {p : P} (h : faceJoin f A ≤ p) (hp : p ∈ generatedSupport f) :
    (((augmentationComponent (k := k) f A).app p).hom
      (structureMapLinear (faceModule (k := k) f A) h
        (HookInfinity.birth (R := k) (faceJoin f A))) : k) = 1 := by
  have hnat := (augmentationComponent (k := k) f A).naturality (homOfLE h)
  have hv := congrArg (fun α => α.hom (HookInfinity.birth (R := k) (faceJoin f A))) hnat
  have hmove : ((augmentationComponent (k := k) f A).app p).hom
      (structureMapLinear (faceModule (k := k) f A) h
        (HookInfinity.birth (R := k) (faceJoin f A))) =
      structureMapLinear
        (SupportInterval.module (generatedSupport f) (generatedSupport_ordConnected f)) h
        (((augmentationComponent (k := k) f A).app (faceJoin f A)).hom
          (HookInfinity.birth (R := k) (faceJoin f A))) := by
    simpa [structureMapLinear, structureMap] using hv.symm
  rw [hmove, SupportInterval.structureMap_val]
  simp only [hp, if_pos, one_mul]
  change (((HookInfinity.fromBirth (faceJoin f A)
      (SupportInterval.module (generatedSupport f) (generatedSupport_ordConnected f))
      (SupportInterval.one (generatedSupport f) (faceJoin_mem_support f A))).app
      (faceJoin f A)).hom (HookInfinity.birth (R := k) (faceJoin f A)) : k) = 1
  rw [HookInfinity.fromBirth_birth]
  simp [SupportInterval.one]

/-- The generator occurrences active at the persistence index `p`. -/
abbrev ActiveIndex {m : ℕ} (f : Fin m → P) (p : P) :=
  {i : Fin m // f i ≤ p}

/-- The simplex on the active generator occurrences, as a subcomplex of `Fin m`.
Repeated values of `f` remain different vertices because membership is indexed by `Fin m`. -/
def activeComplex {m : ℕ} (f : Fin m → P) (p : P) :
    PreAbstractSimplicialComplex (Fin m) where
  faces := {s | s.Nonempty ∧ ∀ i ∈ s, f i ≤ p}
  isRelLowerSet_faces := by
    intro s hs
    constructor
    · exact hs.1
    · intro t hts ht
      exact ⟨ht, fun i hi => hs.2 i (hts hi)⟩

/-- A face born by `p` is precisely a face of the active-occurrence simplex. -/
noncomputable def activeFaceEquiv {m r : ℕ} (f : Fin m → P) (p : P) :
    {A : FaceIndex m r // faceJoin f A ≤ p} ≃
      TDA.Simplicial.Face (activeComplex f p) r where
  toFun A := ⟨A.1.1, ⟨(face_nonempty A.1), (faceJoin_le_iff f A.1 p).mp A.2⟩, A.1.2⟩
  invFun s := ⟨⟨s.1, s.2.2⟩, (faceJoin_le_iff f ⟨s.1, s.2.2⟩ p).mpr
      (by intro i hi; exact s.2.1.2 i hi)⟩
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    rfl

/-- Active-face equivalence commutes with the ordered deletion maps. -/
theorem activeFaceEquiv_eraseFaceAt {m r : ℕ} (f : Fin m → P) (p : P)
    (A : FaceIndex m (r + 1)) (j : Fin (r + 2)) (h : faceJoin f A ≤ p) :
    activeFaceEquiv f p ⟨eraseFaceAt A j,
      (faceJoin_mono f A (eraseFaceAt A j) (eraseFaceAt_subset A j)).trans h⟩ =
      TDA.Simplicial.deletedFace (activeComplex f p) r
        (activeFaceEquiv f p ⟨A, h⟩) j := by
  apply Subtype.ext
  rfl

/-- Evaluation of a graded-free face sum is the chain module on active faces. -/
noncomputable def freeTermEvaluationEquiv {m r : ℕ} (f : Fin m → P) (p : P) :
    (freeTerm (k := k) f r).obj p ≃ₗ[k]
      TDA.Simplicial.Chain (activeComplex f p) k r := by
  classical
  exact (GradedFree.fiberEquiv (R := k) (faceGenerators f r) p).trans
    (Finsupp.domLCongr (activeFaceEquiv f p))

/-- Evaluation of the degree-`r` term is the chain module on active faces. -/
noncomputable def termEvaluationEquiv {m r : ℕ} (f : Fin m → P) (p : P) :
    (term (k := k) f r).obj p ≃ₗ[k]
      TDA.Simplicial.Chain (activeComplex f p) k r :=
  ((termBiproductIso (k := k) f r).app p).toLinearEquiv.trans
    (freeTermEvaluationEquiv (k := k) f p)

@[simp] theorem termEvaluationEquiv_apply {m r : ℕ} (f : Fin m → P) (p : P)
    (x : (term (k := k) f r).obj p) :
    termEvaluationEquiv (k := k) f p (r := r) x =
      freeTermEvaluationEquiv (k := k) f p
        (((termBiproductIso (k := k) f r).app p).toLinearEquiv x) := rfl

/-- The face generator at its birth represents the corresponding simplicial basis face. -/
@[simp] theorem termEvaluationEquiv_faceGenerator {m r : ℕ} (f : Fin m → P)
    (p : P) (A : FaceIndex m r) (h : faceJoin f A ≤ p) :
    termEvaluationEquiv (k := k) f p (r := r)
      (structureMapLinear (term (k := k) f r) h
        ((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A).app
          (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A)))) =
        Finsupp.single (activeFaceEquiv f p ⟨A, h⟩) (1 : k) := by
  classical
  let x := (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A).app
    (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A))
  have hbirth : (termToFree (k := k) f r).app (faceJoin f A) x =
      GradedFree.birth (R := k) (faceGenerators f r) A := by
    change ((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A ≫
      termToFree (k := k) f r).app (faceJoin f A)).hom
        (HookInfinity.birth (R := k) (faceJoin f A)) = _
    rw [termToFree_ι]
    simp [HookInfinity.fromBirth_birth]
  have hmove : (termToFree (k := k) f r).app p
      (structureMapLinear (term (k := k) f r) h x) =
        GradedFree.generator (R := k) (faceGenerators f r) A h := by
    have hn := termToFree (k := k) f r |>.naturality (homOfLE h)
    have hv := congrArg (fun α => α.hom x) hn
    have hs : structureMapLinear (freeTerm (k := k) f r) h
        ((termToFree (k := k) f r).app (faceJoin f A) x) =
          (termToFree (k := k) f r).app p (structureMapLinear (term (k := k) f r) h x) := by
      simpa [structureMapLinear, structureMap] using hv.symm
    rw [← hs, hbirth, GradedFree.generator_eq_structureMap]
  have hgen : GradedFree.fiberEquiv (R := k) (faceGenerators f r) p
      (GradedFree.generator (R := k) (faceGenerators f r) A h) =
        Finsupp.single ⟨A, h⟩ (1 : k) := by
    change Finsupp.subtypeDomain (fun g : FaceIndex m r => faceJoin f g ≤ p)
      (Finsupp.single A (1 : k)) = _
    apply Finsupp.ext
    intro B
    simp [Finsupp.subtypeDomain_apply, Finsupp.single_apply, Subtype.ext_iff]
  calc
    _ = freeTermEvaluationEquiv (k := k) f p
        (GradedFree.generator (R := k) (faceGenerators f r) A h) := by
          rw [termEvaluationEquiv_apply]
          change freeTermEvaluationEquiv (k := k) f p
            ((termToFree (k := k) f r).app p
              (structureMapLinear (term (k := k) f r) h x)) = _
          rw [hmove]
    _ = Finsupp.single (activeFaceEquiv f p ⟨A, h⟩) (1 : k) := by
          rw [freeTermEvaluationEquiv]
          change Finsupp.domLCongr (M := k) (R := k) (activeFaceEquiv f p)
            (GradedFree.fiberEquiv (R := k) (faceGenerators f r) p
              (GradedFree.generator (R := k) (faceGenerators f r) A h)) = _
          rw [hgen, Finsupp.domLCongr_single]

/-- A biproduct inclusion commutes with structure maps on a summand. -/
theorem biproduct_ι_structureMap {m r : ℕ} (f : Fin m → P)
    (A : FaceIndex m r) {a b : P} (hab : a ≤ b)
    (x : (faceModule (k := k) f A).obj a) :
    structureMapLinear (term (k := k) f r) hab
        ((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A).app a x) =
      (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A).app b
        (structureMapLinear (faceModule (k := k) f A) hab x) := by
  classical
  have hn := (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B) A)
    |>.naturality (homOfLE hab)
  have hv := congrArg (fun α => α.hom x) hn
  simpa [structureMapLinear, structureMap] using hv

/-- On a degree-zero face generator, the evaluated augmentation is coefficient sum. -/
theorem augmentation_faceGenerator_val {m : ℕ} (f : Fin m → P) (p : P)
    (A : FaceIndex m 0) (h : faceJoin f A ≤ p) (hp : p ∈ generatedSupport f) :
    (((augmentation (k := k) f).app p).hom
      (structureMapLinear (term (k := k) f 0) h
        ((biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A).app
          (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A)))) : k) =
      TDA.Simplicial.zeroChainSum (activeComplex f p) k
        (termEvaluationEquiv (k := k) f p (r := 0)
          (structureMapLinear (term (k := k) f 0) h
            ((biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A).app
              (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A))))) := by
  rw [biproduct_ι_structureMap]
  have hιapp : ((augmentation (k := k) f).app p).hom
      ((biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A).app p
        (structureMapLinear (faceModule (k := k) f A) h
          (HookInfinity.birth (R := k) (faceJoin f A)))) =
        ((augmentationComponent (k := k) f A).app p).hom
          (structureMapLinear (faceModule (k := k) f A) h
            (HookInfinity.birth (R := k) (faceJoin f A))) := by
    have heq := congrArg (fun α => α.app p) (augmentation_ι (k := k) f A)
    have hv := congrArg (fun α => α.hom
      (structureMapLinear (faceModule (k := k) f A) h
        (HookInfinity.birth (R := k) (faceJoin f A)))) heq
    simpa [ModuleCat.comp_apply] using hv
  rw [hιapp]
  have hcv := augmentationComponent_val (k := k) f A h hp
  rw [hcv]
  rw [← biproduct_ι_structureMap (k := k) f A (hab := h)]
  rw [termEvaluationEquiv_faceGenerator]
  rw [TDA.Simplicial.zeroChainSum_single]

/-- The evaluated augmentation is coefficient sum whenever the support fiber is nonzero. -/
theorem augmentation_val {m : ℕ} (f : Fin m → P) (p : P)
    (hp : p ∈ generatedSupport f) (x : (term (k := k) f 0).obj p) :
    (((augmentation (k := k) f).app p).hom x : k) =
      TDA.Simplicial.zeroChainSum (activeComplex f p) k
        (termEvaluationEquiv (k := k) f p (r := 0) x) := by
  classical
  let E := termEvaluationEquiv (k := k) f p (r := 0)
  let augVal : (term (k := k) f 0).obj p →ₗ[k] k :=
    (Submodule.subtype (SupportInterval.fiber (k := k) (generatedSupport f) p)).comp
      ((augmentation (k := k) f).app p).hom
  have hmap : augVal.comp E.symm.toLinearMap =
      TDA.Simplicial.zeroChainSum (activeComplex f p) k := by
    apply Finsupp.lhom_ext
    intro σ a
    let A := (activeFaceEquiv f p).symm σ
    let xA := structureMapLinear (term (k := k) f 0) A.property
      ((biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A.1).app
        (faceJoin f A.1) (HookInfinity.birth (R := k) (faceJoin f A.1)))
    have hface : activeFaceEquiv f p ⟨A.1, A.property⟩ = σ := by
      simpa [A] using (Equiv.apply_symm_apply (activeFaceEquiv f p) σ)
    have hgen : E xA = Finsupp.single σ (1 : k) := by
      simpa [E, xA, hface] using
        termEvaluationEquiv_faceGenerator (k := k) f p A.1 A.property
    have hinv : E.symm (Finsupp.single σ (1 : k)) = xA := by
      apply E.injective
      simpa [hgen]
    have hval : augVal xA = 1 := by
      have h := augmentation_faceGenerator_val (k := k) f p A.1 A.property hp
      rw [hgen, TDA.Simplicial.zeroChainSum_single] at h
      simpa [augVal, xA] using h
    have hcoeff : Finsupp.single σ a = a • Finsupp.single σ (1 : k) := by
      ext τ
      simp [Finsupp.smul_single]
    change augVal (E.symm (Finsupp.single σ a)) =
      TDA.Simplicial.zeroChainSum (activeComplex f p) k (Finsupp.single σ a)
    calc
      augVal (E.symm (Finsupp.single σ a)) = a := by
        rw [hcoeff, map_smul, hinv]
        simp [hval]
      _ = TDA.Simplicial.zeroChainSum (activeComplex f p) k (Finsupp.single σ a) := by
        rw [TDA.Simplicial.zeroChainSum_single]
  have hx := LinearMap.congr_fun hmap (E x)
  have hcancel : E.symm (E x) = x := E.symm_apply_apply x
  change augVal (E.symm (E x)) =
    TDA.Simplicial.zeroChainSum (activeComplex f p) k (E x) at hx
  rw [hcancel] at hx
  simpa [augVal, E] using hx

/-- The degree-zero face indexed by a single generator occurrence. -/
def singletonFaceIndex {m : ℕ} (i : Fin m) : FaceIndex m 0 := by
  refine ⟨{i}, ?_⟩
  simp

@[simp] theorem faceJoin_singleton {m : ℕ} (f : Fin m → P) (i : Fin m) :
    faceJoin f (singletonFaceIndex i) = f i := by
  simp [faceJoin, singletonFaceIndex]

/-- The augmentation is surjective at every index of its support. -/
theorem augmentation_surjective_at {m : ℕ} (f : Fin m → P) (p : P) :
    Function.Surjective ((augmentation (k := k) f).app p).hom := by
  classical
  by_cases hp : p ∈ generatedSupport f
  · intro y
    have hsupport := hp
    obtain ⟨i, hi⟩ := hp
    let A := singletonFaceIndex i
    have hA : faceJoin f A ≤ p := by simpa [A] using hi
    let x := structureMapLinear (term (k := k) f 0) hA
      ((biproduct.ι (fun B : FaceIndex m 0 => faceModule (k := k) f B) A).app
        (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A)))
    have hunit : (((augmentation (k := k) f).app p).hom x : k) = 1 := by
      have h := augmentation_faceGenerator_val (k := k) f p A hA hsupport
      rw [termEvaluationEquiv_faceGenerator, TDA.Simplicial.zeroChainSum_single] at h
      exact h
    refine ⟨(y : k) • x, ?_⟩
    apply Subtype.ext
    change (((augmentation (k := k) f).app p).hom ((y : k) • x) : k) = (y : k)
    simp [hunit]
  · intro y
    refine ⟨0, ?_⟩
    apply Subtype.ext
    have hy := SupportInterval.val_eq_zero (k := k) (generatedSupport f) hp y
    simpa using hy.symm

/-- Evaluating the differential at the birth of one face gives its signed deletion sum. -/
theorem differential_faceBirth {m : ℕ} (f : Fin m → P) (r : ℕ)
    (A : FaceIndex m (r + 1)) :
    ((differential (k := k) f r).app (faceJoin f A)).hom
        ((biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) f B) A).app
          (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A))) =
      ∑ j : Fin (r + 2), (-1 : k) ^ (j : ℕ) •
        (biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B)
          (eraseFaceAt A j)).app (faceJoin f A)
          (structureMapLinear (faceModule (k := k) f (eraseFaceAt A j))
                (faceJoin_mono f A (eraseFaceAt A j) (eraseFaceAt_subset A j))
            (HookInfinity.birth (R := k) (faceJoin f (eraseFaceAt A j)))) := by
  classical
  have hcomp := congrArg (fun α => α.app (faceJoin f A))
    (differential_ι (k := k) f r A)
  have hv := congrArg (fun α => α.hom (HookInfinity.birth (R := k) (faceJoin f A))) hcomp
  simpa [ModuleCat.comp_apply, signedDeletionAt_birth] using hv

/-- Under evaluation, the actual differential is the ordered simplicial boundary. -/
theorem termEvaluationEquiv_differential_face {m : ℕ} (f : Fin m → P) (p : P)
    (r : ℕ) (A : FaceIndex m (r + 1)) (h : faceJoin f A ≤ p) :
    termEvaluationEquiv (k := k) f p (r := r)
        (((differential (k := k) f r).app p).hom
          (structureMapLinear (term (k := k) f (r + 1)) h
            ((biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) f B) A).app
              (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A))))) =
      TDA.Simplicial.boundary (activeComplex f p) k r
        (Finsupp.single (activeFaceEquiv f p ⟨A, h⟩) (1 : k)) := by
  classical
  let x := (biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) f B) A).app
    (faceJoin f A) (HookInfinity.birth (R := k) (faceJoin f A))
  have hnat := (differential (k := k) f r).naturality (homOfLE h)
  have hn : ((differential (k := k) f r).app p).hom
      (structureMapLinear (term (k := k) f (r + 1)) h x) =
        structureMapLinear (term (k := k) f r) h
          (((differential (k := k) f r).app (faceJoin f A)).hom x) := by
    have hv := congrArg (fun α => α.hom x) hnat
    simpa [structureMapLinear, structureMap] using hv.symm
  have hterm (j : Fin (r + 2)) :
      termEvaluationEquiv (k := k) f p (r := r)
          (structureMapLinear (term (k := k) f r) h
            ((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B)
              (eraseFaceAt A j)).app (faceJoin f A)
              (structureMapLinear (faceModule (k := k) f (eraseFaceAt A j))
                (faceJoin_mono f A (eraseFaceAt A j) (eraseFaceAt_subset A j))
                (HookInfinity.birth (R := k) (faceJoin f (eraseFaceAt A j)))))) =
        Finsupp.single
          (TDA.Simplicial.deletedFace (activeComplex f p) r
            (activeFaceEquiv f p ⟨A, h⟩) j) (1 : k) := by
    rw [biproduct_ι_structureMap]
    have hjoin := faceJoin_mono f A (eraseFaceAt A j) (eraseFaceAt_subset A j)
    have htotal := hjoin.trans h
    have hcomp : structureMapLinear (faceModule (k := k) f (eraseFaceAt A j))
        htotal (HookInfinity.birth (R := k) (faceJoin f (eraseFaceAt A j))) =
      structureMapLinear (faceModule (k := k) f (eraseFaceAt A j)) h
        (structureMapLinear (faceModule (k := k) f (eraseFaceAt A j)) hjoin
          (HookInfinity.birth (R := k) (faceJoin f (eraseFaceAt A j)))) := by
      exact congrArg (fun g => g
        (HookInfinity.birth (R := k) (faceJoin f (eraseFaceAt A j)))
      ) (structureMapLinear_comp (faceModule (k := k) f (eraseFaceAt A j)) hjoin h)
    rw [← hcomp]
    rw [← biproduct_ι_structureMap (k := k) f (eraseFaceAt A j)
      (hab := htotal)]
    rw [termEvaluationEquiv_faceGenerator]
    rw [activeFaceEquiv_eraseFaceAt]
  calc
    _ = termEvaluationEquiv (k := k) f p (r := r)
          (structureMapLinear (term (k := k) f r) h
            (((differential (k := k) f r).app (faceJoin f A)).hom x)) := by
          rw [hn]
    _ = TDA.Simplicial.boundary (activeComplex f p) k r
          (Finsupp.single (activeFaceEquiv f p ⟨A, h⟩) (1 : k)) := by
          rw [differential_faceBirth]
          calc
            _ = ∑ j : Fin (r + 2), (-1 : k) ^ (j : ℕ) •
                termEvaluationEquiv (k := k) f p (r := r)
                  (structureMapLinear (term (k := k) f r) h
                    ((biproduct.ι (fun B : FaceIndex m r => faceModule (k := k) f B)
                      (eraseFaceAt A j)).app (faceJoin f A)
                      (structureMapLinear (faceModule (k := k) f (eraseFaceAt A j))
                        (faceJoin_mono f A (eraseFaceAt A j) (eraseFaceAt_subset A j))
                        (HookInfinity.birth (R := k) (faceJoin f (eraseFaceAt A j)))))) := by
                  simp only [map_sum, map_smul]
            _ = ∑ j : Fin (r + 2), (-1 : k) ^ (j : ℕ) •
                Finsupp.single
                  (TDA.Simplicial.deletedFace (activeComplex f p) r
                    (activeFaceEquiv f p ⟨A, h⟩) j) (1 : k) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hterm]
            _ = TDA.Simplicial.boundary (activeComplex f p) k r
                (Finsupp.single (activeFaceEquiv f p ⟨A, h⟩) (1 : k)) := by
                  rw [TDA.Simplicial.boundary_single]
                  simp [Finset.smul_sum, Finsupp.smul_single]

/-- The evaluated categorical differential is the simplicial boundary on every chain. -/
theorem termEvaluationEquiv_differential {m : ℕ} (f : Fin m → P) (p : P)
    (r : ℕ) (x : (term (k := k) f (r + 1)).obj p) :
    termEvaluationEquiv (k := k) f p (r := r)
        (((differential (k := k) f r).app p).hom x) =
      TDA.Simplicial.boundary (activeComplex f p) k r
        (termEvaluationEquiv (k := k) f p (r := r + 1) x) := by
  classical
  let E₁ := termEvaluationEquiv (k := k) f p (r := r + 1)
  let E₀ := termEvaluationEquiv (k := k) f p (r := r)
  let d : TDA.Simplicial.Chain (activeComplex f p) k (r + 1) →ₗ[k]
      TDA.Simplicial.Chain (activeComplex f p) k r :=
    E₀.toLinearMap.comp
      ((((differential (k := k) f r).app p).hom).comp E₁.symm.toLinearMap)
  have hd : d = TDA.Simplicial.boundary (activeComplex f p) k r := by
    apply Finsupp.lhom_ext
    intro σ a
    let A := (activeFaceEquiv f p).symm σ
    let xA := structureMapLinear (term (k := k) f (r + 1)) A.property
      ((biproduct.ι (fun B : FaceIndex m (r + 1) => faceModule (k := k) f B)
        A.1).app (faceJoin f A.1) (HookInfinity.birth (R := k) (faceJoin f A.1)))
    have hface : activeFaceEquiv f p ⟨A.1, A.property⟩ = σ := by
      simpa [A] using (Equiv.apply_symm_apply (activeFaceEquiv f p) σ)
    have hgen : E₁ xA = Finsupp.single σ (1 : k) := by
      simpa [E₁, xA, hface] using
        termEvaluationEquiv_faceGenerator (k := k) f p A.1 A.property
    have hinv : E₁.symm (Finsupp.single σ (1 : k)) = xA := by
      apply E₁.injective
      simpa [hgen]
    have hbase : E₀ (((differential (k := k) f r).app p).hom xA) =
        TDA.Simplicial.boundary (activeComplex f p) k r
          (Finsupp.single σ (1 : k)) := by
      simpa [E₀, xA, hface] using
        termEvaluationEquiv_differential_face (k := k) f p r A.1 A.property
    have hcoeff : Finsupp.single σ a = a • Finsupp.single σ (1 : k) := by
      ext τ
      simp [Finsupp.smul_single]
    change d (Finsupp.single σ a) =
      TDA.Simplicial.boundary (activeComplex f p) k r (Finsupp.single σ a)
    calc
      d (Finsupp.single σ a) = a • d (Finsupp.single σ (1 : k)) := by
        rw [hcoeff]
        rw [map_smul]
      _ = a • TDA.Simplicial.boundary (activeComplex f p) k r
          (Finsupp.single σ (1 : k)) := by
        change a • E₀ (((differential (k := k) f r).app p).hom
          (E₁.symm (Finsupp.single σ (1 : k)))) = _
        rw [hinv, hbase]
      _ = TDA.Simplicial.boundary (activeComplex f p) k r (Finsupp.single σ a) := by
        rw [hcoeff, map_smul]
  have hx := LinearMap.congr_fun hd (E₁ x)
  change E₀ (((differential (k := k) f r).app p).hom
    (E₁.symm (E₁ x))) = _ at hx
  rw [LinearEquiv.symm_apply_apply] at hx
  change E₀ (((differential (k := k) f r).app p).hom x) = _
  exact hx

/-- The generated support consists exactly of indices with an active occurrence. -/
theorem mem_generatedSupport_iff_active {m : ℕ} (f : Fin m → P) (p : P) :
    p ∈ generatedSupport f ↔ Nonempty (ActiveIndex f p) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨⟨i, hi⟩⟩
  · rintro ⟨⟨i, hi⟩⟩
    exact ⟨i, hi⟩

/-- With no active occurrence, every evaluated resolution term is zero. -/
theorem term_eq_zero_of_no_active {m r : ℕ} (f : Fin m → P) (p : P)
    (h : ¬ Nonempty (ActiveIndex f p)) (x : (term (k := k) f r).obj p) : x = 0 := by
  apply (termEvaluationEquiv (k := k) f p (r := r)).injective
  apply Finsupp.ext
  intro σ
  obtain ⟨i, hi⟩ := σ.2.1.1.exists_mem
  exact (h ⟨⟨i, σ.2.1.2 i hi⟩⟩).elim

/-- The degree-`r` term vanishes when it asks for more occurrences than `Fin m` contains. -/
theorem term_isZero_of_degree_ge {m r : ℕ} (f : Fin m → P) (hmr : m ≤ r) :
    IsZero (term (k := k) f r) := by
  rw [Functor.isZero_iff]
  intro p
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro x y
  have hzero (z : (term (k := k) f r).obj p) : z = 0 := by
    apply (termEvaluationEquiv (k := k) f p (r := r)).injective
    apply Finsupp.ext
    intro σ
    have hcard := Finset.card_le_univ σ.1
    simp only [Fintype.card_fin] at hcard
    have hdeg : σ.1.card = r + 1 := σ.2.2
    omega
  exact (hzero x).trans (hzero y).symm

/-- The zero-generator family has empty generated support. -/
theorem generatedSupport_fin_zero (f : Fin 0 → P) : generatedSupport f = ∅ := by
  ext p
  simp [generatedSupport]

/-- The support module of the empty indexed family is the zero persistence module. -/
theorem generatedSupport_fin_zero_module_isZero (f : Fin 0 → P) :
    IsZero (SupportInterval.module (k := k) (generatedSupport f)
      (generatedSupport_ordConnected f)) := by
  rw [Functor.isZero_iff]
  intro p
  change IsZero (ModuleCat.of k
    (SupportInterval.fiber (k := k) (generatedSupport f) p))
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (SupportInterval.fiber (k := k) (generatedSupport f) p)
  constructor
  intro x y
  apply Subtype.ext
  have hx := SupportInterval.val_eq_zero (k := k) (generatedSupport f)
    (by rw [generatedSupport_fin_zero]; simp) x
  have hy := SupportInterval.val_eq_zero (k := k) (generatedSupport f)
    (by rw [generatedSupport_fin_zero]; simp) y
  exact hx.trans hy.symm

/-- The active-occurrence complex is coned by any active occurrence. -/
theorem activeComplex_isApexCone {m : ℕ} (f : Fin m → P) (p : P)
    [Nonempty (ActiveIndex f p)] :
    ∃ v, TDA.Simplicial.IsApexCone (activeComplex f p) v := by
  classical
  letI : LinearOrder (ActiveIndex f p) := inferInstance
  letI : Finite (ActiveIndex f p) := Finite.of_fintype _
  obtain ⟨v, hv⟩ := Finite.exists_min (fun w : ActiveIndex f p => w)
  refine ⟨v.1, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change ({v.1} : Finset (Fin m)).Nonempty ∧ _
    simp [v.2]
  · intro s hs
    change (insert v.1 s).Nonempty ∧ ∀ i ∈ insert v.1 s, f i ≤ p
    refine ⟨by simp, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact v.2
    · exact hs.2 i hi
  · intro s hs w hw
    exact hv ⟨w, hs.2 w hw⟩

/-- Positive-degree cycles on the active-occurrence simplex are boundaries. -/
theorem activeComplex_positive_exact {m : ℕ} (f : Fin m → P) (p : P)
    [Nonempty (ActiveIndex f p)] (r : ℕ)
    (c : TDA.Simplicial.Chain (activeComplex f p) k (r + 1))
    (hc : TDA.Simplicial.boundary (activeComplex f p) k r c = 0) :
    ∃ d : TDA.Simplicial.Chain (activeComplex f p) k (r + 2),
      TDA.Simplicial.boundary (activeComplex f p) k (r + 1) d = c := by
  classical
  obtain ⟨v, hK⟩ := activeComplex_isApexCone f p
  refine ⟨hK.coneOperator k (r + 1) c, ?_⟩
  have hcontract := hK.boundary_coneOperator_add k r c
  rw [hc, map_zero, add_zero] at hcontract
  exact hcontract

/-- Degree-zero cycles in the augmented active-occurrence complex are boundaries. -/
theorem activeComplex_zero_exact {m : ℕ} (f : Fin m → P) (p : P)
    [Nonempty (ActiveIndex f p)]
    (c : TDA.Simplicial.Chain (activeComplex f p) k 0)
    (hc : TDA.Simplicial.zeroChainSum (activeComplex f p) k c = 0) :
    ∃ d : TDA.Simplicial.Chain (activeComplex f p) k 1,
      TDA.Simplicial.boundary (activeComplex f p) k 0 d = c := by
  classical
  obtain ⟨v, hK⟩ := activeComplex_isApexCone f p
  refine ⟨hK.coneOperator k 0 c, ?_⟩
  rw [hK.boundary_coneOperator_zero k c, hc]
  simp

/-- Every positive-degree cycle in the evaluated resolution is a boundary. -/
theorem differential_exact_at_succ {m : ℕ} (f : Fin m → P) (p : P) (r : ℕ)
    (x : (term (k := k) f (r + 1)).obj p)
    (hx : ((differential (k := k) f r).app p).hom x = 0) :
    ∃ y : (term (k := k) f (r + 2)).obj p,
      ((differential (k := k) f (r + 1)).app p).hom y = x := by
  classical
  by_cases ha : Nonempty (ActiveIndex f p)
  · have hmap := termEvaluationEquiv_differential (k := k) f p r x
    have hcycle : TDA.Simplicial.boundary (activeComplex f p) k r
        (termEvaluationEquiv (k := k) f p (r := r + 1) x) = 0 := by
      rw [← hmap, hx]
      simp
    letI : Nonempty (ActiveIndex f p) := ha
    obtain ⟨z, hz⟩ := activeComplex_positive_exact (k := k) f p r
      (termEvaluationEquiv (k := k) f p (r := r + 1) x) hcycle
    let y := (termEvaluationEquiv (k := k) f p (r := r + 2)).symm z
    refine ⟨y, ?_⟩
    apply (termEvaluationEquiv (k := k) f p (r := r + 1)).injective
    calc
      termEvaluationEquiv (k := k) f p (r := r + 1)
          (((differential (k := k) f (r + 1)).app p).hom y) =
          TDA.Simplicial.boundary (activeComplex f p) k (r + 1)
            (termEvaluationEquiv (k := k) f p (r := r + 2) y) :=
        termEvaluationEquiv_differential (k := k) f p (r + 1) y
      _ = TDA.Simplicial.boundary (activeComplex f p) k (r + 1) z := by simp [y]
      _ = termEvaluationEquiv (k := k) f p (r := r + 1) x := hz
  · have hx0 := term_eq_zero_of_no_active (k := k) f p ha x
    exact ⟨0, by simp [hx0]⟩

/-- Two consecutive alternating differentials compose to zero. -/
theorem differential_comp_differential {m : ℕ} (f : Fin m → P) (r : ℕ) :
    differential (k := k) f (r + 1) ≫ differential (k := k) f r = 0 := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (termEvaluationEquiv (k := k) f p (r := r)).injective
  simp only [NatTrans.comp_app, ModuleCat.comp_apply, NatTrans.app_zero,
    ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  change termEvaluationEquiv (k := k) f p (r := r)
      (((differential (k := k) f r).app p).hom
        (((differential (k := k) f (r + 1)).app p).hom x)) = 0
  calc
    _ = TDA.Simplicial.boundary (activeComplex f p) k r
          (termEvaluationEquiv (k := k) f p (r := r + 1)
            (((differential (k := k) f (r + 1)).app p).hom x)) :=
          termEvaluationEquiv_differential (k := k) f p r _
    _ = TDA.Simplicial.boundary (activeComplex f p) k r
          (TDA.Simplicial.boundary (activeComplex f p) k (r + 1)
            (termEvaluationEquiv (k := k) f p (r := r + 2) x)) := by
          rw [termEvaluationEquiv_differential]
    _ = 0 := by
          have hz := LinearMap.congr_fun
            (TDA.Simplicial.boundary_comp_boundary (activeComplex f p) k r)
            (termEvaluationEquiv (k := k) f p (r := r + 2) x)
          simpa using hz

/-- The augmentation annihilates the first alternating differential. -/
theorem differential_comp_augmentation {m : ℕ} (f : Fin m → P) :
    differential (k := k) f 0 ≫ augmentation (k := k) f = 0 := by
  apply NatTrans.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (((augmentation (k := k) f).app p).hom
    (((differential (k := k) f 0).app p).hom x) : k) = 0
  by_cases hp : p ∈ generatedSupport f
  · have hval := augmentation_val (k := k) f p hp
      (((differential (k := k) f 0).app p).hom x)
    rw [termEvaluationEquiv_differential] at hval
    have hzero : TDA.Simplicial.zeroChainSum (activeComplex f p) k
        (TDA.Simplicial.boundary (activeComplex f p) k 0
          (termEvaluationEquiv (k := k) f p (r := 1) x)) = 0 := by
      have hz := LinearMap.congr_fun
        (TDA.Simplicial.zeroChainSum_boundary (activeComplex f p) k)
        (termEvaluationEquiv (k := k) f p (r := 1) x)
      simpa [LinearMap.comp_apply] using hz
    rw [hval]
    exact hzero
  · exact SupportInterval.val_eq_zero (k := k) (generatedSupport f) hp
      (((augmentation (k := k) f).app p).hom
        (((differential (k := k) f 0).app p).hom x))

/-- The augmented evaluated sequence is exact at degree zero. -/
theorem augmentation_exact_at_zero {m : ℕ} (f : Fin m → P) (p : P)
    (x : (term (k := k) f 0).obj p)
    (hx : ((augmentation (k := k) f).app p).hom x = 0) :
    ∃ y : (term (k := k) f 1).obj p,
      ((differential (k := k) f 0).app p).hom y = x := by
  classical
  by_cases hp : p ∈ generatedSupport f
  · have hsum : TDA.Simplicial.zeroChainSum (activeComplex f p) k
        (termEvaluationEquiv (k := k) f p (r := 0) x) = 0 := by
      have hval := augmentation_val (k := k) f p hp x
      have hv := congrArg (fun z : SupportInterval.fiber (k := k)
          (generatedSupport f) p => (z : k)) hx
      rw [← hval]
      simpa using hv
    letI : Nonempty (ActiveIndex f p) :=
      (mem_generatedSupport_iff_active f p).mp hp
    obtain ⟨z, hz⟩ := activeComplex_zero_exact (k := k) f p
      (termEvaluationEquiv (k := k) f p (r := 0) x) hsum
    let y := (termEvaluationEquiv (k := k) f p (r := 1)).symm z
    refine ⟨y, ?_⟩
    apply (termEvaluationEquiv (k := k) f p (r := 0)).injective
    calc
      termEvaluationEquiv (k := k) f p (r := 0)
          (((differential (k := k) f 0).app p).hom y) =
          TDA.Simplicial.boundary (activeComplex f p) k 0
            (termEvaluationEquiv (k := k) f p (r := 1) y) :=
        termEvaluationEquiv_differential (k := k) f p 0 y
      _ = TDA.Simplicial.boundary (activeComplex f p) k 0 z := by simp [y]
      _ = termEvaluationEquiv (k := k) f p (r := 0) x := hz
  · have hactive : ¬ Nonempty (ActiveIndex f p) := by
      intro ha
      exact hp ((mem_generatedSupport_iff_active f p).mpr ha)
    have hx0 := term_eq_zero_of_no_active (k := k) f p hactive x
    exact ⟨0, by simp [hx0]⟩

/-- At each index, the augmented join-indexed sequence is exact at every term and onto its
support-module target. The first kernel is at `C₀`; the remaining kernels are indexed by `r`. -/
theorem resolution_pointwise_exact_at {m : ℕ} (f : Fin m → P) (p : P) :
    Function.Surjective ((augmentation (k := k) f).app p).hom ∧
      (∀ x : (term (k := k) f 0).obj p,
        ((augmentation (k := k) f).app p).hom x = 0 →
          ∃ y : (term (k := k) f 1).obj p,
            ((differential (k := k) f 0).app p).hom y = x) ∧
      (∀ r (x : (term (k := k) f (r + 1)).obj p),
        ((differential (k := k) f r).app p).hom x = 0 →
          ∃ y : (term (k := k) f (r + 2)).obj p,
            ((differential (k := k) f (r + 1)).app p).hom y = x) := by
  refine ⟨augmentation_surjective_at (k := k) f p, ?_, ?_⟩
  · intro x hx
    exact augmentation_exact_at_zero (k := k) f p x hx
  · intro r x hx
    exact differential_exact_at_succ (k := k) f p r x hx

/-- Every evaluated face-sum term vanishes for the empty indexed family. -/
theorem term_fin_zero_eq_zero (f : Fin 0 → P) (r : ℕ) (p : P)
    (x : (term (k := k) f r).obj p) : x = 0 := by
  exact term_eq_zero_of_no_active (k := k) f p
    (by rintro ⟨⟨i, hi⟩⟩; exact Fin.elim0 i) x

end TDA.Persistence.GeneratedUpsetResolution
