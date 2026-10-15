import TDA.Filtration.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite-face chain bridge prototype

The basis uses precisely the faces of a preabstract simplicial complex. The generic
chain-complex constructor below accepts a square-zero proof; it does not prove the
simplicial boundary theorem. The only concrete differential here is for small fixtures.
-/

universe u

namespace TDA.Simplicial

open CategoryTheory Module

variable {V : Type u} [LinearOrder V]

/-- Actual nonempty `(n+1)`-vertex faces, with no ambient singleton completion. -/
abbrev Face (K : PreAbstractSimplicialComplex V) (n : ℕ) :=
  {s : Finset V // s ∈ K ∧ s.card = n + 1}

/-- A finite total face set is a separate hypothesis from each face being a `Finset`. -/
abbrev TotalFace (K : PreAbstractSimplicialComplex V) := {s : Finset V // s ∈ K}

instance faceFiniteOfTotalFinite (K : PreAbstractSimplicialComplex V) (n : ℕ)
    [Finite (TotalFace K)] : Finite (Face K n) :=
  Finite.of_injective (fun s => (⟨s.1, s.2.1⟩ : TotalFace K)) (by
    intro a b h
    have hv : a.1 = b.1 := congrArg (fun t : TotalFace K => t.1) h
    exact Subtype.ext hv)

/-- Free oriented chains on actual faces, with the orientation from the ambient order. -/
abbrev Chain (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] (n : ℕ) :=
  Face K n →₀ R

/-- The canonical face basis; this does not require finite ambient vertices. -/
noncomputable def faceBasis (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] (n : ℕ) :
    Basis (Face K n) R (Chain K R n) := Finsupp.basisSingleOne

/-- A face inclusion keeps the same ordered vertex set and its orientation. -/
def faceIncl {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (n : ℕ) :
    Face K n → Face L n := fun s => ⟨s.1, h s.2.1, s.2.2⟩

/-- Inclusion of the corresponding free modules. -/
noncomputable def chainIncl {K L : PreAbstractSimplicialComplex V} (R : Type*) [Ring R]
    (h : K ≤ L) (n : ℕ) : Chain K R n →ₗ[R] Chain L R n :=
  Finsupp.lmapDomain R R (faceIncl h n)

omit [LinearOrder V] in
theorem chainIncl_id (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R]
    (n : ℕ) : chainIncl R (le_refl K) n = LinearMap.id := by
  have he : faceIncl (le_refl K) n = (id : Face K n → Face K n) := by
    funext s
    rfl
  simp [chainIncl, he]

omit [LinearOrder V] in
theorem chainIncl_comp {K L M : PreAbstractSimplicialComplex V} (R : Type*) [Ring R]
    (h : K ≤ L) (g : L ≤ M) (n : ℕ) :
    chainIncl R (h.trans g) n = (chainIncl R g n).comp (chainIncl R h n) := by
  have he : faceIncl (h.trans g) n = faceIncl g n ∘ faceIncl h n := by
    funext s
    rfl
  simpa [chainIncl, he] using
    (Finsupp.lmapDomain_comp (M := R) (R := R) (faceIncl h n) (faceIncl g n))

/-- Conditional packaging only: the supplied `sq` is not constructed here. -/
noncomputable def packagedComplex (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R]
    (d : ∀ n, ModuleCat.of R (Chain K R (n + 1)) ⟶ ModuleCat.of R (Chain K R n))
    (sq : ∀ n, d (n + 1) ≫ d n = 0) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (Chain K R n)) d sq

/-- Conditional chain-map packaging, with differential commutation supplied by the caller. -/
noncomputable def packagedInclusion {K L : PreAbstractSimplicialComplex V} (R : Type*) [Ring R]
    (dK : ∀ n, ModuleCat.of R (Chain K R (n + 1)) ⟶ ModuleCat.of R (Chain K R n))
    (sqK : ∀ n, dK (n + 1) ≫ dK n = 0)
    (dL : ∀ n, ModuleCat.of R (Chain L R (n + 1)) ⟶ ModuleCat.of R (Chain L R n))
    (sqL : ∀ n, dL (n + 1) ≫ dL n = 0) (h : K ≤ L)
    (comm : ∀ n, ModuleCat.ofHom (chainIncl R h (n + 1)) ≫ dL n =
      dK n ≫ ModuleCat.ofHom (chainIncl R h n)) :
    packagedComplex K R dK sqK ⟶ packagedComplex L R dL sqL :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (chainIncl R h n)) (by
    intro n
    simpa [packagedComplex] using comm n)

/-- The existing ModuleCat kernel/image-inside-kernel quotient, for any supplied
chain complex. This identifies ordinary homology rather than defining a new quotient. -/
noncomputable def homologyKernelQuotient (R : Type*) [Ring R]
    (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    C.homology n ≅ ModuleCat.of R
      (LinearMap.ker (C.sc n).g.hom ⧸ LinearMap.range (C.sc n).moduleCatToCycles) :=
  (C.sc n).moduleCatHomologyIso

/-- The degree-zero short complex for a fixture with no edges. Both maps are zero,
as required by ordinary, unaugmented homology. -/
noncomputable def zeroBoundaryH0 (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (0 : Chain K R 1 →ₗ[R] Chain K R 0)
    (0 : Chain K R 0 →ₗ[R] Chain K R 0) (by simp)

/-- Ordinary H₀ of a zero-boundary fixture equals its degree-zero chains. -/
noncomputable def zeroBoundaryH0Iso (K : PreAbstractSimplicialComplex V)
    (R : Type*) [Ring R] :
    (zeroBoundaryH0 K R).homology ≅ ModuleCat.of R (Chain K R 0) :=
  (ShortComplex.LeftHomologyData.ofZeros (zeroBoundaryH0 K R) rfl rfl).homologyIso

instance emptyFaceIsEmpty (n : ℕ) : IsEmpty (Face (⊥ : PreAbstractSimplicialComplex V) n) :=
  ⟨fun s => (Filtration.mem_bot_iff s.1).mp s.2.1⟩

omit [LinearOrder V] in
/-- The empty precomplex has zero chains in every degree. -/
theorem emptyChain_eq_zero (R : Type*) [Ring R] (n : ℕ)
    (c : Chain (⊥ : PreAbstractSimplicialComplex V) R n) : c = 0 :=
  Subsingleton.elim _ _

omit [LinearOrder V] in
/-- Its ordinary unaugmented H₀ is the zero module. -/
theorem emptyH0_eq_zero (R : Type*) [Ring R]
    (c : (zeroBoundaryH0 (⊥ : PreAbstractSimplicialComplex V) R).homology) : c = 0 := by
  apply (zeroBoundaryH0Iso (⊥ : PreAbstractSimplicialComplex V) R).toLinearEquiv.injective
  exact Subsingleton.elim _ _

instance singletonFaceZeroSubsingleton (x : V) :
    Subsingleton (Face (Filtration.singletonFace x) 0) := by
  constructor
  intro a b
  apply Subtype.ext
  calc
    a.1 = {x} := (Filtration.mem_singletonFace_iff x a.1).mp a.2.1
    _ = b.1 := ((Filtration.mem_singletonFace_iff x b.1).mp b.2.1).symm

/-- The only degree-zero basis face of a singleton complex. -/
def singletonVertex (x : V) : Face (Filtration.singletonFace x) 0 :=
  ⟨{x}, (Filtration.mem_singletonFace_iff x {x}).mpr rfl, by simp⟩

instance singletonFaceHigherIsEmpty (x : V) (n : ℕ) :
    IsEmpty (Face (Filtration.singletonFace x) (n + 1)) := by
  constructor
  intro s
  have hs := (Filtration.mem_singletonFace_iff x s.1).mp s.2.1
  have hc : 1 = n + 1 + 1 := by simpa [hs] using s.2.2
  omega

omit [LinearOrder V] in
/-- A singleton has no positive-degree chains. -/
theorem singletonHigherChain_eq_zero (x : V) (R : Type*) [Ring R] (n : ℕ)
    (c : Chain (Filtration.singletonFace x) R (n + 1)) : c = 0 :=
  Subsingleton.elim _ _

/-- The ordinary H₀ of an isolated vertex is exactly its coefficient module. -/
noncomputable def singletonH0Iso (x : V) (R : Type u) [Ring R] :
    (zeroBoundaryH0 (Filtration.singletonFace x) R).homology ≅ ModuleCat.of R R :=
  (zeroBoundaryH0Iso (Filtration.singletonFace x) R).trans
    ((Finsupp.uniqueLinearEquiv R R (singletonVertex x)).toModuleIso)

section Triangle

/-- The complete triangle on the three ambient vertices; each face below is an actual face. -/
private def triangleK : PreAbstractSimplicialComplex (Fin 3) := ⊤

private def vertex (i : Fin 3) : Face triangleK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 3)).Nonempty; simp, by simp⟩

private def edge01 : Face triangleK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def edge02 : Face triangleK 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def edge12 : Face triangleK 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangle : Face triangleK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

/-- Every actual edge of this finite complex is one of the three listed edges. -/
private theorem edge_cover :
    ∀ e : Face triangleK 1, e = edge01 ∨ e = edge02 ∨ e = edge12 := by
  have h : ∀ s : Finset (Fin 3), s.card = 2 →
      s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2} := by decide
  intro e
  rcases h e.1 e.2.2 with h | h | h
  · left; exact Subtype.ext h
  · right; left; exact Subtype.ext h
  · right; right; exact Subtype.ext h

/-- Oriented edge boundary, using the fixed order `0 < 1 < 2`. -/
private noncomputable def edgeBoundary (e : Face triangleK 1) : Chain triangleK ℤ 0 :=
  if e = edge01 then Finsupp.single (vertex 1) 1 - Finsupp.single (vertex 0) 1
  else if e = edge02 then Finsupp.single (vertex 2) 1 - Finsupp.single (vertex 0) 1
  else Finsupp.single (vertex 2) 1 - Finsupp.single (vertex 1) 1

/-- The boundary on the actual finite edge basis, extended linearly. -/
private noncomputable def signedD1 : Chain triangleK ℤ 1 →ₗ[ℤ] Chain triangleK ℤ 0 :=
  Finsupp.linearCombination ℤ edgeBoundary

/-- `[1,2] - [0,2] + [0,1]` as an actual edge chain. -/
private noncomputable def triangleBoundary : Chain triangleK ℤ 1 :=
  Finsupp.single edge12 1 - Finsupp.single edge02 1 + Finsupp.single edge01 1

private theorem signed_triangle_cancels : signedD1 triangleBoundary = 0 := by
  classical
  have h₁ : edge12 ≠ edge01 := by decide
  have h₂ : edge12 ≠ edge02 := by decide
  have h₃ : edge02 ≠ edge01 := by decide
  simp [signedD1, triangleBoundary, edgeBoundary, h₁, h₂, h₃,
    Finsupp.linearCombination_single]

/-- The triangular 2-simplex has precisely the required signed edge boundary. -/
private noncomputable def signedD2 : Chain triangleK ℤ 2 →ₗ[ℤ] Chain triangleK ℤ 1 :=
  Finsupp.linearCombination ℤ (fun _ => triangleBoundary)

private theorem triangle_boundary_formula :
    signedD2 (Finsupp.single triangle 1) = triangleBoundary := by
  simp [signedD2, Finsupp.linearCombination_single]

private theorem triangle_boundary_squared :
    signedD1 (signedD2 (Finsupp.single triangle 1)) = 0 := by
  rw [triangle_boundary_formula]
  exact signed_triangle_cancels

omit [LinearOrder V] in
/-- `toMatrix` uses a `CommRing`, an enumerated domain face basis, and a finite codomain
face basis. `Fintype.ofFinite` is possible for theory but is not an executable enumeration. -/
private theorem matrix_coordinate {K : PreAbstractSimplicialComplex V} (R : Type*)
    [CommRing R] (n : ℕ) [Fintype (Face K (n + 1))]
    [DecidableEq (Face K (n + 1))] [Finite (Face K n)]
    (d : Chain K R (n + 1) →ₗ[R] Chain K R n)
    (i : Face K n) (j : Face K (n + 1)) :
    LinearMap.toMatrix (faceBasis K R (n + 1)) (faceBasis K R n) d i j =
      (faceBasis K R n).repr (d ((faceBasis K R (n + 1)) j)) i := by
  exact LinearMap.toMatrix_apply _ _ _ _ _

/-- A signed matrix coordinate on the actual three-edge/two-dimensional triangle fixture. -/
private theorem signed_matrix_entry :
    ∃ (M : Matrix (Face triangleK 0) (Face triangleK 1) ℤ),
      M (vertex 1) edge01 = 1 ∧ M (vertex 0) edge01 = -1 := by
  classical
  letI : Fintype (Face triangleK 1) := Fintype.ofFinite _
  let M := LinearMap.toMatrix (faceBasis triangleK ℤ 1) (faceBasis triangleK ℤ 0) signedD1
  refine ⟨M, ?_, ?_⟩
  · change (LinearMap.toMatrix (faceBasis triangleK ℤ 1)
      (faceBasis triangleK ℤ 0) signedD1) (vertex 1) edge01 = 1
    rw [LinearMap.toMatrix_apply]
    simp [faceBasis, signedD1, edgeBoundary, edge01, vertex,
      Finsupp.linearCombination_single]
  · change (LinearMap.toMatrix (faceBasis triangleK ℤ 1)
      (faceBasis triangleK ℤ 0) signedD1) (vertex 0) edge01 = -1
    rw [LinearMap.toMatrix_apply]
    simp [faceBasis, signedD1, edgeBoundary, edge01, vertex,
      Finsupp.linearCombination_single]

/-- A one-edge subcomplex in the same three-vertex ambient type. -/
private def edgeK : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ {0, 1}}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun _ hts ht => ⟨ht, hts.trans hs.2⟩⟩

private def edgeVertex (i : Fin 3) (hi : i ∈ ({0, 1} : Finset (Fin 3))) :
    Face edgeK 0 :=
  ⟨{i}, ⟨Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩, by simp⟩

private def edgeFace : Face edgeK 1 :=
  ⟨{0, 1}, ⟨by decide, Finset.Subset.refl _⟩, by decide⟩

private theorem edgeFace_unique (e : Face edgeK 1) : e = edgeFace := by
  have h : ∀ s : Finset (Fin 3), s.card = 2 → s ⊆ {0, 1} → s = {0, 1} := by decide
  exact Subtype.ext (h e.1 e.2.2 e.2.1.2)

private noncomputable def edgeD1 : Chain edgeK ℤ 1 →ₗ[ℤ] Chain edgeK ℤ 0 :=
  Finsupp.linearCombination ℤ (fun _ =>
    Finsupp.single (edgeVertex 1 (by simp)) 1 -
    Finsupp.single (edgeVertex 0 (by simp)) 1)

/-- A nonzero inclusion square: the edge differential agrees with the triangle
differential under the same-ambient face inclusion. -/
private theorem edge_triangle_square :
    (chainIncl ℤ (show edgeK ≤ triangleK from le_top) 0).comp edgeD1 =
      signedD1.comp (chainIncl ℤ (show edgeK ≤ triangleK from le_top) 1) := by
  classical
  apply Finsupp.lhom_ext
  intro e a
  rw [edgeFace_unique e]
  simp [edgeD1, signedD1, chainIncl, faceIncl, edgeBoundary, edgeFace,
    edgeVertex, edge01, vertex, Finsupp.linearCombination_single,
    Finsupp.mapDomain_sub, Finsupp.mapDomain_single]

end Triangle

end TDA.Simplicial
