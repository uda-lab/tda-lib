import TDA.Simplicial.VertexMap

/-!
# Client statements of the vertex map face conditions

Regression fixtures for #1286, family 12 of the downstream-use audit (#1207). Each statement is
written as a downstream client writes it: the file opens no scope and declares no instance, and
the finite images `Finset.image` on `Fin 3` are elaborated with the decidable equality of the
vertex type; every proof is a direct application of a library theorem.

* The face condition of a vertex map between complexes on `Fin 3`.
* The criterion for the image complex of a map of vertices to lie in a complex, for a plain
  function and for a vertex map.
-/

namespace TDA.Simplicial.VertexMapClientExamples

/-- The image of a face under a vertex map of complexes on `Fin 3` is a face. -/
theorem fin_three_map_face (K L : PreAbstractSimplicialComplex (Fin 3)) (f : VertexMap K L)
    (s : Finset (Fin 3)) (hs : s ∈ K) : s.image f.toFun ∈ L :=
  f.map_face_image s hs

/-- A function of `Fin 3` maps the complex `K` into `L` exactly when it maps every face into a
face. -/
theorem fin_three_map_le_iff (K L : PreAbstractSimplicialComplex (Fin 3)) (r : Fin 3 → Fin 3) :
    PreAbstractSimplicialComplex.map K r ≤ L ↔ ∀ s ∈ K, s.image r ∈ L :=
  map_le_iff r

/-- The same criterion for a vertex map of complexes on `Fin 3`. -/
theorem fin_three_vertexMap_map_le_iff (K L : PreAbstractSimplicialComplex (Fin 3))
    (f : VertexMap K L) :
    PreAbstractSimplicialComplex.map K f ≤ L ↔ ∀ s ∈ K, s.image f ∈ L :=
  f.map_le_iff

end TDA.Simplicial.VertexMapClientExamples
