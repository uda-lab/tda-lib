import TDA.Topology.SubdivisionRealization

/-!
# Natural iterated last vertices

A fixed order at each depth makes the maps on a complex and its subcomplex agree on their common
labels.
-/

namespace TDA.Topology.SubdivisionRealization

open CategoryTheory TDA.Simplicial TDA.Topology.SubdivisionRealization
noncomputable section
universe u

variable {V : Type u}

/-- A fixed order on finite face labels, independent of the chosen complex. -/
noncomputable abbrev faceLinearOrder (X : Type*) [Fintype X] : LinearOrder (Finset X) :=
  LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective

/-- The original order at depth zero and a common face order at positive depths. -/
scoped instance vertexLinearOrder [Fintype V] [LinearOrder V] : (n : ℕ) → LinearOrder (Vertex V n)
  | 0 => ‹LinearOrder V›
  | n + 1 => faceLinearOrder (Vertex V n)

/-- An inhabited original label type supplies labels at every depth. -/
scoped instance vertexNonempty [Nonempty V] : (n : ℕ) → Nonempty (Vertex V n)
  | 0 => ‹Nonempty V›
  | n + 1 => ⟨(∅ : Finset (Vertex V n))⟩

/-- Taking the union of a flag preserves containment. -/
theorem flagUnion_mono {X : Type*} {F G : Finset (Finset X)} (h : F ⊆ G) : flagUnion F ⊆ flagUnion G := by
  classical
  intro i hi
  obtain ⟨A, hA, hv⟩ := Finset.mem_biUnion.mp hi
  exact subset_flagUnion (h hA) hv

/-- A subface has its original vertices in the original face of its coface. -/
theorem originalFace_mono : ∀ (n : ℕ) {F G : Finset (Vertex V n)}, F ⊆ G → originalFace n F ⊆ originalFace n G
  | 0, _, _, h => h
  | n + 1, _, _, h => originalFace_mono n (flagUnion_mono h)

variable [Fintype V] [LinearOrder V] [Nonempty V]

/-- The iterated last vertex as a function of labels alone. -/
def lastVertexLabel : (n : ℕ) → Vertex V n → V
  | 0 => id
  | n + 1 => fun A => lastVertexLabel n (lastVertex A)

/-- Compose last-vertex maps from depth `n` back to the original complex. -/
def iteratedLastVertex (K : PreAbstractSimplicialComplex V) : (n : ℕ) → VertexMap (complex K n) K
  | 0 => VertexMap.id K
  | n + 1 => VertexMap.comp (lastVertexMap (complex K n)) (iteratedLastVertex K n)

/-- The iterated last vertex depends only on its label and subdivision depth. -/
theorem iteratedLastVertex_apply (K : PreAbstractSimplicialComplex V) :
    ∀ n (w : Vertex V n), iteratedLastVertex K n w = lastVertexLabel n w := by
  intro n
  induction n with
  | zero => exact fun _ => rfl
  | succ n ih => exact fun w => ih (lastVertex w)

/-- The iterated last vertex belongs to the original face. -/
theorem lastVertexLabel_mem (K : PreAbstractSimplicialComplex V) :
    ∀ n (F : Finset (Vertex V n)), F ∈ complex K n → ∀ w ∈ F, lastVertexLabel n w ∈ originalFace n F := by
  intro n
  induction n with
  | zero => exact fun _ _ _ hw => hw
  | succ n ih =>
    intro F hF w hw
    have hn := ((complex K n).isRelLowerSet_faces (hF.2.1 w hw).1).1
    apply ih (flagUnion F) (hF.2.1 _ (flagUnion_mem hF)).1
    apply subset_flagUnion hw
    exact lastVertex_of_nonempty w hn ▸ Finset.max'_mem w hn

/-- Last vertices commute with the literal inclusion at each subdivision depth. -/
theorem iteratedLastVertex_naturality {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (n : ℕ) :
    VertexMap.comp (inclusionVertexMap (complex_mono h n)) (iteratedLastVertex L n) =
    VertexMap.comp (iteratedLastVertex K n) (inclusionVertexMap h) := by
  ext v
  exact (iteratedLastVertex_apply L n v).trans (iteratedLastVertex_apply K n v).symm

/-- The iterated last-vertex map induces an isomorphism in each homology degree. -/
theorem isIso_iteratedLastVertex (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] (k : ℕ) :
    ∀ n, IsIso (simplicialHomologyMap R (iteratedLastVertex K n) k) := by
  intro n
  induction n with
  | zero =>
    change IsIso (simplicialHomologyMap R (VertexMap.id K) k)
    rw [simplicialHomologyMap_id]
    infer_instance
  | succ n ih =>
    let : LinearOrder (Finset (Vertex V n)) := vertexLinearOrder (V := V) (n + 1)
    let : IsIso (simplicialHomologyMap R (lastVertexMap (complex K n)) k) :=
      inferInstanceAs (IsIso (barycentricHomologyIso R (complex K n) k).hom)
    change IsIso (simplicialHomologyMap R (VertexMap.comp (lastVertexMap (complex K n)) (iteratedLastVertex K n)) k)
    rw [simplicialHomologyMap_comp]
    exact IsIso.comp_isIso


/-- Subdivision preserves a same-label inclusion. -/
theorem subdivision_mono {X : Type*} [Fintype X] {K L : PreAbstractSimplicialComplex X} (h : K ≤ L) : barycentricSubdivision K ≤ barycentricSubdivision L :=
  TDA.Filtration.SubdivisionRips.subdivision_mono h le_rfl

variable {I : Type u} [Fintype I] [LinearOrder I] [Nonempty I]
local instance : LinearOrder (Finset I) := faceLinearOrder I

/-- Subdivide the flag complex another `n` times, using the same labels for every subcomplex. -/
abbrev subdividedFlags (K : PreAbstractSimplicialComplex I) (n : ℕ) := complex (barycentricSubdivision K) n

/-- Return from a refined flag to an original vertex. -/
def flagLastVertex (K : PreAbstractSimplicialComplex I) (n : ℕ) : VertexMap (subdividedFlags K n) K :=
  VertexMap.comp (iteratedLastVertex (barycentricSubdivision K) n) (lastVertexMap K)

/-- The map from refined flags to the original complex induces a homology isomorphism. -/
theorem isIso_flagLastVertex (K : PreAbstractSimplicialComplex I) (R : Type*) [Ring R] (k n : ℕ) :
    IsIso (simplicialHomologyMap R (flagLastVertex K n) k) := by
  let := isIso_iteratedLastVertex (barycentricSubdivision K) R k n
  let : IsIso (simplicialHomologyMap R (lastVertexMap K) k) :=
    inferInstanceAs (IsIso (barycentricHomologyIso R K k).hom)
  rw [flagLastVertex, simplicialHomologyMap_comp]
  infer_instance

/-- The last-vertex square for the common positive-depth subdivision commutes on vertex maps. -/
theorem flagLastVertex_naturality {K L : PreAbstractSimplicialComplex I} (h : K ≤ L) (n : ℕ) :
    VertexMap.comp (inclusionVertexMap (complex_mono (subdivision_mono h) n)) (flagLastVertex L n) =
      VertexMap.comp (flagLastVertex K n) (inclusionVertexMap h) := by
  ext v
  change lastVertex (iteratedLastVertex (barycentricSubdivision L) n v) = lastVertex (iteratedLastVertex (barycentricSubdivision K) n v)
  rw [iteratedLastVertex_apply, iteratedLastVertex_apply]

end
end TDA.Topology.SubdivisionRealization
