import TDA.Persistence.IncidenceVertexTensor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# The categorical vertex tensor

The character coinvariants from `IncidenceVertexTensor` form an additive functor
on the actual incidence-algebra modules.  The balanced quotient property makes
this functor left adjoint to restriction along the vertex character.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.IncidenceVertexTensorFunctor

open CategoryTheory
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceVertexTensor

variable {k : Type u} [Field k] {S : Type} [Lattice S] [Finite S]

noncomputable section

local instance : Fintype S := Fintype.ofFinite S
local instance : DecidableLE S := Classical.decRel _
local instance : DecidableLT S := Classical.decRel _
local instance : DecidableEq S := Classical.decEq _
local instance : DecidableEq (WithTop S) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset S) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop S × WithTop S => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset S) := Classical.decRel _
local instance : DecidableLT (PairPoset S) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset S) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset S) := Classical.decEq _
local instance : Fintype (ComparablePair S) := Fintype.ofFinite _

abbrev Incidence := FiniteRankProjectiveEndAlgebra.Incidence (k := k) (S := S)

variable (v : StrictVertex S)
variable {M : ModuleCat (Incidence (k := k) (S := S))}

abbrev restrictedScalarsStructure (M : ModuleCat (Incidence (k := k) (S := S))) :
    Module k M := Module.compHom M (algebraMap k (Incidence (k := k) (S := S)))

local instance restrictedScalars (M : ModuleCat (Incidence (k := k) (S := S))) :
    Module k M := restrictedScalarsStructure (k := k) (S := S) M

theorem restrictedScalarsTower (M : ModuleCat (Incidence (k := k) (S := S))) :
    IsScalarTower k (Incidence (k := k) (S := S)) M :=
  IsScalarTower.of_compHom k (Incidence (k := k) (S := S)) M

local instance scalarTower (M : ModuleCat (Incidence (k := k) (S := S))) :
    IsScalarTower k (Incidence (k := k) (S := S)) M :=
  restrictedScalarsTower (k := k) (S := S) M

/-- The character relation submodule on an arbitrary incidence-algebra module. -/
abbrev relation (M : ModuleCat (Incidence (k := k) (S := S))) : Submodule k M :=
  vertexRelation (k := k) (R := Incidence (k := k) (S := S)) (N := M)
    (vertexCharacter (k := k) (S := S) v)

/-- The vertex coinvariants of an incidence-algebra module, bundled as a `k`-module. -/
abbrev coinvariants (M : ModuleCat (Incidence (k := k) (S := S))) : ModuleCat k :=
  ModuleCat.of k (VertexCoinvariants (k := k) (R := Incidence (k := k) (S := S))
    (N := M) (vertexCharacter (k := k) (S := S) v))

/-- The restricted `k`-module structure used by the vertex relation quotient on a bundled
incidence-algebra module. -/
abbrev restrictedKModule (M : ModuleCat (Incidence (k := k) (S := S))) : ModuleCat k :=
  ModuleCat.of k M

/-- A scalar-compatible additive equivalence from restriction of scalars.  Keeping the source
module abstract fixes the restricted scalar structure before any concrete carrier is unfolded. -/
def restrictedKLinearEquiv {N : Type u} [AddCommGroup N] [Module k N]
    (e : M ≃+ N)
    (h : ∀ (c : k) (x : M), e ((algebraMap k (Incidence (k := k) (S := S)) c) • x) =
      c • e x) : ↑(restrictedKModule (k := k) (S := S) M) ≃ₗ[k] N :=
  e.toLinearEquiv h

/-- Transport character coinvariants through a scalar-compatible incidence-module equivalence. -/
def coinvariantsEquiv {N : Type u} [AddCommGroup N] [Module k N]
    [Module (Incidence (k := k) (S := S)) N]
    (e : M ≃+ N)
    (hk : ∀ (c : k) (x : M), e ((algebraMap k (Incidence (k := k) (S := S)) c) • x) =
      c • e x)
    (hA : ∀ (a : Incidence (k := k) (S := S)) (x : M), e (a • x) = a • e x) :
    coinvariants (k := k) (S := S) v M ≃ₗ[k]
      VertexCoinvariants (k := k) (R := Incidence (k := k) (S := S)) (N := N)
        (vertexCharacter (k := k) (S := S) v) := by
  let eL := restrictedKLinearEquiv (k := k) (S := S) e hk
  apply Submodule.Quotient.equiv _ _ eL
  simp only [relation, vertexRelation, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨x, ⟨⟨a, m⟩, rfl⟩, rfl⟩
    refine ⟨(a, e m), ?_⟩
    change a • e m - vertexCharacter (k := k) (S := S) v a • e m =
      e (a • m - algebraMap k (Incidence (k := k) (S := S))
        (vertexCharacter (k := k) (S := S) v a) • m)
    rw [map_sub, hA, hk]
  · rintro ⟨⟨a, m⟩, rfl⟩
    refine ⟨a • e.symm m - vertexCharacter (k := k) (S := S) v a • e.symm m,
      ⟨(a, e.symm m), rfl⟩, ?_⟩
    change e (a • e.symm m - algebraMap k (Incidence (k := k) (S := S))
      (vertexCharacter (k := k) (S := S) v a) • e.symm m) =
        a • m - vertexCharacter (k := k) (S := S) v a • m
    rw [map_sub, hA, hk, e.apply_symm_apply]

/-- The transported quotient equivalence sends a quotient class to the class of its image. -/
@[simp] theorem coinvariantsEquiv_mkQ {N : Type u} [AddCommGroup N] [Module k N]
    [Module (Incidence (k := k) (S := S)) N]
    (e : M ≃+ N)
    (hk : ∀ (c : k) (x : M), e ((algebraMap k (Incidence (k := k) (S := S)) c) • x) =
      c • e x)
    (hA : ∀ (a : Incidence (k := k) (S := S)) (x : M), e (a • x) = a • e x)
    (x : M) :
    coinvariantsEquiv (k := k) (S := S) v e hk hA
      ((relation (k := k) (S := S) v M).mkQ x) =
        (vertexRelation (k := k) (R := Incidence (k := k) (S := S))
          (N := N) (vertexCharacter (k := k) (S := S) v)).mkQ (e x) := by
  have he : (restrictedKLinearEquiv (k := k) (S := S) e hk) x = e x := by
    change (e.toLinearEquiv hk) x = e x
    exact congrFun (AddEquiv.coe_toLinearEquiv e hk) x
  simp only [coinvariantsEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_mkQ]
  exact congrArg (fun y : N =>
    (vertexRelation (k := k) (R := Incidence (k := k) (S := S))
      (N := N) (vertexCharacter (k := k) (S := S) v)).mkQ y) he

private def restrictMap {M N : ModuleCat (Incidence (k := k) (S := S))}
    (f : M ⟶ N) : M →ₗ[k] N := f.hom.restrictScalars k

private theorem relation_map_le {M N : ModuleCat (Incidence (k := k) (S := S))}
    (f : M ⟶ N) : relation (k := k) (S := S) v M ≤
      Submodule.comap (restrictMap (k := k) (S := S) f) (relation (k := k) (S := S) v N) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨a, m⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨(a, f.hom m), ?_⟩
  change a • f.hom m - vertexCharacter (k := k) (S := S) v a • f.hom m =
    (restrictMap (k := k) (S := S) f)
      (a • m - vertexCharacter (k := k) (S := S) v a • m)
  rw [map_sub]
  change a • f.hom m - vertexCharacter (k := k) (S := S) v a • f.hom m =
    f.hom (a • m) - (restrictMap (k := k) (S := S) f)
      (vertexCharacter (k := k) (S := S) v a • m)
  rw [← f.hom.map_smul]
  change f.hom (a • m) - vertexCharacter (k := k) (S := S) v a •
      (restrictMap (k := k) (S := S) f m) = _
  rw [← (restrictMap (k := k) (S := S) f).map_smul]

/-- The map on vertex coinvariants induced by an actual incidence-linear map. -/
def map {M N : ModuleCat (Incidence (k := k) (S := S))} (f : M ⟶ N) :
    coinvariants (k := k) (S := S) v M ⟶ coinvariants (k := k) (S := S) v N :=
  ModuleCat.ofHom <| (relation (k := k) (S := S) v M).mapQ
    (relation (k := k) (S := S) v N) (restrictMap (k := k) (S := S) f)
    (relation_map_le (k := k) (S := S) v f)

@[simp] theorem map_mkQ {M N : ModuleCat (Incidence (k := k) (S := S))}
    (f : M ⟶ N) (m : M) :
    map (k := k) (S := S) v f ((relation (k := k) (S := S) v M).mkQ m) =
      (relation (k := k) (S := S) v N).mkQ (f.hom m) := rfl

/-- The categorical vertex tensor, with object map the actual quotient and maps descended from
incidence-algebra homomorphisms. -/
def vertexTensor : ModuleCat (Incidence (k := k) (S := S)) ⥤ ModuleCat k where
  obj := coinvariants (k := k) (S := S) v
  map := map (k := k) (S := S) v
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) v M).mkQ_surjective q
    rw [← hm]
    rfl
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) v M).mkQ_surjective q
    rw [← hm]
    rfl

/-- The quotient class of a module element, bundled in the actual functor value. -/
def mk (M : ModuleCat (Incidence (k := k) (S := S))) (x : M) :
    (vertexTensor (k := k) (S := S) v).obj M :=
  (relation (k := k) (S := S) v M).mkQ x

/-- The equivalence on actual coinvariant classes induced by a scalar-compatible module
equivalence. -/
@[simp] theorem coinvariantsEquiv_mk {N : Type u} [AddCommGroup N] [Module k N]
    [Module (Incidence (k := k) (S := S)) N]
    (e : M ≃+ N)
    (hk : ∀ (c : k) (x : M), e ((algebraMap k (Incidence (k := k) (S := S)) c) • x) =
      c • e x)
    (hA : ∀ (a : Incidence (k := k) (S := S)) (x : M), e (a • x) = a • e x)
    (x : M) :
    coinvariantsEquiv (k := k) (S := S) v e hk hA
      (mk (k := k) (S := S) v M x) =
        (vertexRelation (k := k) (R := Incidence (k := k) (S := S))
          (N := N) (vertexCharacter (k := k) (S := S) v)).mkQ (e x) := by
  exact coinvariantsEquiv_mkQ (k := k) (S := S) (v := v) e hk hA x

instance vertexTensor_additive : (vertexTensor (k := k) (S := S) v).Additive where
  map_add {M N} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) v M).mkQ_surjective q
    rw [← hm]
    change (relation (k := k) (S := S) v N).mkQ ((f + g).hom m) =
      (relation (k := k) (S := S) v N).mkQ (f.hom m) +
        (relation (k := k) (S := S) v N).mkQ (g.hom m)
    rw [show (f + g).hom = f.hom + g.hom by rfl]
    simp

@[simp] theorem vertexTensor_map_apply_mkQ {M N : ModuleCat (Incidence (k := k) (S := S))}
    (f : M ⟶ N) (m : M) :
    (vertexTensor (k := k) (S := S) v).map f ((relation (k := k) (S := S) v M).mkQ m) =
      (relation (k := k) (S := S) v N).mkQ (f.hom m) := map_mkQ (k := k) (S := S) v f m

/-- The quotient map to vertex coinvariants obeys the actual character relation. -/
@[simp] theorem mkQ_smul (M : ModuleCat (Incidence (k := k) (S := S)))
    (a : Incidence (k := k) (S := S)) (m : M) :
    (relation (k := k) (S := S) v M).mkQ (a • m) =
      vertexCharacter (k := k) (S := S) v a • (relation (k := k) (S := S) v M).mkQ m :=
  vertexRelation_mkQ (k := k) (R := Incidence (k := k) (S := S))
    (N := M) (vertexCharacter (k := k) (S := S) v) a m

/-- Restriction of scalars along the actual vertex character. -/
def characterRestriction : ModuleCat k ⥤ ModuleCat (Incidence (k := k) (S := S)) :=
  ModuleCat.restrictScalars (vertexCharacter (k := k) (S := S) v).toRingHom

/-- Restricting the character module again along `k → A` gives the original `k`-module. -/
private def characterRestrictionKIso (V : ModuleCat k) :
    ((ModuleCat.restrictScalars (algebraMap k (Incidence (k := k) (S := S)))).obj
      ((characterRestriction (k := k) (S := S) v).obj V)) ≅ V := by
  have hgf : RingHom.id k =
      (vertexCharacter (k := k) (S := S) v).toRingHom.comp
        (algebraMap k (Incidence (k := k) (S := S))) := by
    ext c
    simp [vertexCharacter_algebraMap]
  exact (ModuleCat.restrictScalarsComp'App
      (algebraMap k (Incidence (k := k) (S := S)))
      (vertexCharacter (k := k) (S := S) v).toRingHom (RingHom.id k) hgf V).symm ≪≫
    ModuleCat.restrictScalarsId'App (RingHom.id k) rfl V

@[simp] private theorem characterRestrictionKIso_hom_apply (V : ModuleCat k)
    (x : ↑((ModuleCat.restrictScalars (algebraMap k (Incidence (k := k) (S := S)))).obj
      ((characterRestriction (k := k) (S := S) v).obj V))) :
    (characterRestrictionKIso (k := k) (S := S) v V).hom x = x := by
  rfl

private def kLinearOfRestrictedMap {V : ModuleCat k}
    (g : M ⟶ (characterRestriction (k := k) (S := S) v).obj V) : M →ₗ[k] V := by
  exact (((ModuleCat.restrictScalars (algebraMap k (Incidence (k := k) (S := S)))).map g ≫
    (characterRestrictionKIso (k := k) (S := S) v V).hom).hom)

@[simp] private theorem kLinearOfRestrictedMap_apply {V : ModuleCat k}
    (g : M ⟶ (characterRestriction (k := k) (S := S) v).obj V) (m : M) :
    kLinearOfRestrictedMap (k := k) (S := S) v g m = g.hom m := by
  rfl

private def balancedBilinear {V : ModuleCat k}
    (g : M ⟶ (characterRestriction (k := k) (S := S) v).obj V) :
    k →ₗ[k] M →ₗ[k] V where
  toFun x :=
    { toFun := fun m => x • kLinearOfRestrictedMap (k := k) (S := S) v g m
      map_add' := by
        intro m n
        calc
          x • kLinearOfRestrictedMap (k := k) (S := S) v g (m + n) =
              x • (kLinearOfRestrictedMap (k := k) (S := S) v g m +
                kLinearOfRestrictedMap (k := k) (S := S) v g n) := by rw [map_add]
          _ = x • kLinearOfRestrictedMap (k := k) (S := S) v g m +
                x • kLinearOfRestrictedMap (k := k) (S := S) v g n := by rw [smul_add]
      map_smul' := by
        intro c m
        change x • kLinearOfRestrictedMap (k := k) (S := S) v g (c • m) =
          c • (x • kLinearOfRestrictedMap (k := k) (S := S) v g m)
        rw [(kLinearOfRestrictedMap (k := k) (S := S) v g).map_smul]
        exact smul_comm x c _ }
  map_add' x y := by
    ext m
    change (x + y) • kLinearOfRestrictedMap (k := k) (S := S) v g m =
      x • kLinearOfRestrictedMap (k := k) (S := S) v g m +
        y • kLinearOfRestrictedMap (k := k) (S := S) v g m
    rw [add_smul]
  map_smul' c x := by
    ext m
    change (c * x) • kLinearOfRestrictedMap (k := k) (S := S) v g m =
      c • (x • kLinearOfRestrictedMap (k := k) (S := S) v g m)
    rw [mul_smul]

private theorem balancedBilinear_balanced {V : ModuleCat k}
    (g : M ⟶ (characterRestriction (k := k) (S := S) v).obj V)
    (x : k) (a : Incidence (k := k) (S := S)) (m : M) :
    balancedBilinear (k := k) (S := S) v g (x *
      vertexCharacter (k := k) (S := S) v a) m =
      balancedBilinear (k := k) (S := S) v g x (a • m) := by
  have h : kLinearOfRestrictedMap (k := k) (S := S) v g (a • m) =
      vertexCharacter (k := k) (S := S) v a •
        kLinearOfRestrictedMap (k := k) (S := S) v g m := by
    rw [kLinearOfRestrictedMap_apply, kLinearOfRestrictedMap_apply]
    exact g.hom.map_smul a m
  change (x * vertexCharacter (k := k) (S := S) v a) •
      kLinearOfRestrictedMap (k := k) (S := S) v g m =
    x • kLinearOfRestrictedMap (k := k) (S := S) v g (a • m)
  rw [h, mul_smul]

private def fromCharacterRestriction {V : ModuleCat k}
    (g : M ⟶ (characterRestriction (k := k) (S := S) v).obj V) :
    coinvariants (k := k) (S := S) v M ⟶ V := by
  let f := balancedBilinear (k := k) (S := S) v g
  have hbal : IsVertexBalanced (χ := vertexCharacter (k := k) (S := S) v) f :=
    balancedBilinear_balanced (k := k) (S := S) v g
  exact ModuleCat.ofHom <| vertexBalancedFactor
    (χ := vertexCharacter (k := k) (S := S) v) f hbal

private def toCharacterRestriction {V : ModuleCat k}
    (f : coinvariants (k := k) (S := S) v M ⟶ V) :
    M ⟶ (characterRestriction (k := k) (S := S) v).obj V := by
  letI : Module (Incidence (k := k) (S := S)) V :=
    ((characterRestriction (k := k) (S := S) v).obj V).isModule
  exact ModuleCat.ofHom
    { toFun := fun m => f.hom ((relation (k := k) (S := S) v M).mkQ m)
      map_add' := by simp
      map_smul' := by
        intro a m
        change f.hom ((relation (k := k) (S := S) v M).mkQ (a • m)) =
          vertexCharacter (k := k) (S := S) v a •
            f.hom ((relation (k := k) (S := S) v M).mkQ m)
        rw [mkQ_smul]
        simpa only [ModuleCat.restrictScalars.smul_def] using
          f.hom.map_smul (vertexCharacter (k := k) (S := S) v a)
            ((relation (k := k) (S := S) v M).mkQ m) }

@[simp] private theorem toCharacterRestriction_apply {V : ModuleCat k}
    (f : coinvariants (k := k) (S := S) v M ⟶ V) (m : M) :
    (toCharacterRestriction (k := k) (S := S) v f).hom m =
      f.hom ((relation (k := k) (S := S) v M).mkQ m) := rfl

@[simp] private theorem fromCharacterRestriction_apply_mkQ {V : ModuleCat k}
    (g : M ⟶ (characterRestriction (k := k) (S := S) v).obj V) (m : M) :
    (fromCharacterRestriction (k := k) (S := S) v g).hom
      ((relation (k := k) (S := S) v M).mkQ m) =
        kLinearOfRestrictedMap (k := k) (S := S) v g m := by
  change vertexBalancedFactor (χ := vertexCharacter (k := k) (S := S) v)
      (balancedBilinear (k := k) (S := S) v g)
      (balancedBilinear_balanced (k := k) (S := S) v g)
      ((relation (k := k) (S := S) v M).mkQ m) = _
  rw [show (relation (k := k) (S := S) v M).mkQ m =
      vertexPure (χ := vertexCharacter (k := k) (S := S) v) 1 m by simp [vertexPure]]
  simpa [balancedBilinear, kLinearOfRestrictedMap] using vertexBalancedFactor_pure
    (χ := vertexCharacter (k := k) (S := S) v)
    (balancedBilinear (k := k) (S := S) v g)
    (balancedBilinear_balanced (k := k) (S := S) v g) 1 m

/-- The Hom-set equivalence between the actual character coinvariants and restriction along the
actual character. -/
def homEquiv {V : ModuleCat k} :
    (coinvariants (k := k) (S := S) v M ⟶ V) ≃
      (M ⟶ (characterRestriction (k := k) (S := S) v).obj V) where
  toFun := toCharacterRestriction (k := k) (S := S) v
  invFun := fromCharacterRestriction (k := k) (S := S) v
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    obtain ⟨m, hm⟩ := (relation (k := k) (S := S) v M).mkQ_surjective q
    rw [← hm]
    change (fromCharacterRestriction (k := k) (S := S) v
        (toCharacterRestriction (k := k) (S := S) v f)).hom
      ((relation (k := k) (S := S) v M).mkQ m) =
        f.hom ((relation (k := k) (S := S) v M).mkQ m)
    rw [fromCharacterRestriction_apply_mkQ, kLinearOfRestrictedMap_apply,
      toCharacterRestriction_apply]
  right_inv g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (toCharacterRestriction (k := k) (S := S) v
        (fromCharacterRestriction (k := k) (S := S) v g)).hom m = g.hom m
    rw [toCharacterRestriction_apply]
    rw [fromCharacterRestriction_apply_mkQ, kLinearOfRestrictedMap_apply]

private theorem homEquiv_naturality_left_symm {M' : ModuleCat (Incidence (k := k) (S := S))}
    (f : M' ⟶ M) {V : ModuleCat k}
    (g : M ⟶ (characterRestriction (k := k) (S := S) v).obj V) :
    (homEquiv (k := k) (S := S) v (M := M') (V := V)).symm (f ≫ g) =
      map (k := k) (S := S) v f ≫
        (homEquiv (k := k) (S := S) v (M := M) (V := V)).symm g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  obtain ⟨m, hm⟩ := (relation (k := k) (S := S) v M').mkQ_surjective q
  rw [← hm]
  change (fromCharacterRestriction (k := k) (S := S) v (f ≫ g)).hom
      ((relation (k := k) (S := S) v M').mkQ m) =
    ((map (k := k) (S := S) v f ≫
      fromCharacterRestriction (k := k) (S := S) v g).hom)
      ((relation (k := k) (S := S) v M').mkQ m)
  rw [ModuleCat.hom_comp]
  change (fromCharacterRestriction (k := k) (S := S) v (f ≫ g)).hom
      ((relation (k := k) (S := S) v M').mkQ m) =
    (fromCharacterRestriction (k := k) (S := S) v g).hom
      ((vertexTensor (k := k) (S := S) v).map f
        ((relation (k := k) (S := S) v M').mkQ m))
  rw [vertexTensor_map_apply_mkQ (k := k) (S := S) v f m]
  rw [fromCharacterRestriction_apply_mkQ, kLinearOfRestrictedMap_apply,
    fromCharacterRestriction_apply_mkQ, kLinearOfRestrictedMap_apply]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]

private theorem homEquiv_naturality_right {V V' : ModuleCat k}
    (f : coinvariants (k := k) (S := S) v M ⟶ V)
    (g : V ⟶ V') :
    homEquiv (k := k) (S := S) v (M := M) (V := V') (f ≫ g) =
      homEquiv (k := k) (S := S) v (M := M) (V := V) f ≫
        (characterRestriction (k := k) (S := S) v).map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change g.hom (f.hom ((relation (k := k) (S := S) v M).mkQ m)) =
    g.hom (f.hom ((relation (k := k) (S := S) v M).mkQ m))
  rfl

/-- The vertex tensor is left adjoint to restriction along its actual incidence character. -/
def vertexTensorAdjunction :
    vertexTensor (k := k) (S := S) v ⊣ characterRestriction (k := k) (S := S) v :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun M V => homEquiv (k := k) (S := S) v (M := M) (V := V)
    homEquiv_naturality_left_symm := fun f g =>
      homEquiv_naturality_left_symm (k := k) (S := S) v f g
    homEquiv_naturality_right := fun f g =>
      homEquiv_naturality_right (k := k) (S := S) v f g }

instance vertexTensor_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (vertexTensor (k := k) (S := S) v) := by
  have h : Limits.PreservesColimitsOfSize.{0, 0}
      (vertexTensor (k := k) (S := S) v) :=
    (vertexTensorAdjunction (k := k) (S := S) v).leftAdjoint_preservesColimits
  exact h.preservesFiniteColimits

end

end TDA.Persistence.IncidenceVertexTensorFunctor
