import TDA.Simplicial.CollapseCertificate

set_option autoImplicit false

/-!
# Accepted and rejected collapse certificates

The tables are small complexes on `Fin 3`, `Fin 4` and `Fin 5`. `triangle` lists the seven faces
of the full triangle, which is also the squared-grade Čech stage of the obtuse triangle on
`[4, 5)`, and `alphaTable` lists the α stage there: the triangle without the long edge `{0,1}` and
the triangle itself. Every acceptance and rejection is evaluated by `decide +kernel`. Each
rejection also records, by `decide`, the fact about the tables that makes it fail.
-/

namespace TDA.Simplicial.CollapseCertificateExamples

open TDA.Simplicial

/-- The seven faces of the full triangle on `Fin 3`. -/
def triangle : Finset (Finset (Fin 3)) :=
  {{0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}}

/-- The full triangle without the long edge `{0,1}` and the triangle `{0,1,2}`. -/
def alphaTable : Finset (Finset (Fin 3)) :=
  {{0}, {1}, {2}, {0,2}, {1,2}}

/-- The fifteen faces of the full tetrahedron on `Fin 4`. -/
def tetrahedron : Finset (Finset (Fin 4)) :=
  Finset.univ.erase ∅

/-- The thirty-one faces of the full 4-simplex on `Fin 5`. -/
def simplex4 : Finset (Finset (Fin 5)) :=
  Finset.univ.erase ∅

/-- Two triangles `{0,1,2}` and `{0,1,3}` glued along the edge `{0,1}`. -/
def twoTriangles : Finset (Finset (Fin 4)) :=
  {{0}, {1}, {2}, {3}, {0,1}, {0,2}, {1,2}, {0,3}, {1,3}, {0,1,2}, {0,1,3}}

/-- The one-step certificate of the obtuse triangle on `[4, 5)`: the long edge is collapsed
through the triangle, and the end is exactly the α table. -/
theorem checkSteps_triangle_alphaTable :
    checkSteps triangle [({0,1}, {0,1,2})] alphaTable = true := by
  decide +kernel

/-- The full triangle collapses to the vertex `{0}` in three steps. -/
theorem checkSteps_triangle_vertex :
    checkSteps triangle [({1,2}, {0,1,2}), ({1}, {0,1}), ({2}, {0,2})] {{0}} = true := by
  decide +kernel

/-- The full tetrahedron collapses to the vertex `{0}` in seven steps. -/
theorem checkSteps_tetrahedron_vertex :
    checkSteps tetrahedron
      [({1,2,3}, {0,1,2,3}), ({1,2}, {0,1,2}), ({1,3}, {0,1,3}), ({2,3}, {0,2,3}),
        ({1}, {0,1}), ({2}, {0,2}), ({3}, {0,3})] {{0}} = true := by
  decide +kernel

/-- The full 4-simplex collapses to the vertex `{0}` in fifteen steps: each face not containing
`0` is collapsed through the face obtained by adding `0`, from the top dimension down. -/
theorem checkSteps_simplex4_vertex :
    checkSteps simplex4
      [({1,2,3,4}, {0,1,2,3,4}),
        ({1,2,3}, {0,1,2,3}), ({1,2,4}, {0,1,2,4}), ({1,3,4}, {0,1,3,4}), ({2,3,4}, {0,2,3,4}),
        ({1,2}, {0,1,2}), ({1,3}, {0,1,3}), ({1,4}, {0,1,4}), ({2,3}, {0,2,3}), ({2,4}, {0,2,4}),
        ({3,4}, {0,3,4}),
        ({1}, {0,1}), ({2}, {0,2}), ({3}, {0,3}), ({4}, {0,4})] {{0}} = true := by
  decide +kernel

/-- The full triangle collapses onto the edge `{0,2}` in two steps, and onto the spine
`{0,1} ∪ {0,2}` in one. -/
theorem checkSteps_triangle_spine :
    checkSteps triangle [({1,2}, {0,1,2}), ({1}, {0,1})] {{0}, {2}, {0,2}} = true ∧
      checkSteps triangle [({1,2}, {0,1,2})] {{0}, {1}, {2}, {0,1}, {0,2}} = true := by
  decide +kernel

/-- Extra coface: in two triangles glued along `{0,1}`, the edge is not free, because
`{0,1,3}` also strictly contains it. -/
theorem checkSteps_twoTriangles_extra_coface :
    checkSteps twoTriangles [({0,1}, {0,1,2})] ((twoTriangles.erase {0,1}).erase {0,1,2}) =
        false ∧
      ({0,1,3} : Finset (Fin 4)) ∈ twoTriangles := by
  decide +kernel

/-- Coface not present: in the α table the long edge and the triangle are both absent, so the
step of the Čech table is rejected there; the same step is accepted from `triangle`. -/
theorem checkSteps_alphaTable_not_mem :
    checkSteps alphaTable [({0,1}, {0,1,2})] alphaTable = false ∧
      ({0,1,2} : Finset (Fin 3)) ∉ alphaTable := by
  decide +kernel

/-- Reversed pair: `({0,1,2}, {0,1})` lists the coface first, and `{0,1,2} ⊄ {0,1}`. -/
theorem checkSteps_triangle_reversed :
    checkSteps triangle [({0,1,2}, {0,1})] alphaTable = false ∧
      ¬ ({0,1,2} : Finset (Fin 3)) ⊆ {0,1} := by
  decide +kernel

/-- Codimension two: `({0}, {0,1,2})` adds two vertices. On a complex, a pair that is not a cover
also has an intermediate coface; here `{0,1}` is one. -/
theorem checkSteps_triangle_codim_two :
    checkSteps triangle [({0}, {0,1,2})] {{1}, {2}, {0,1}, {0,2}, {1,2}} = false ∧
      (({0,1,2} : Finset (Fin 3)) \ {0}).card = 2 := by
  decide +kernel

/-- Wrong order: the steps of `checkSteps_triangle_vertex` in another order are rejected,
because the vertex `{1}` is not free while the edge `{1,2}` is present. -/
theorem checkSteps_triangle_wrong_order :
    checkSteps triangle [({1}, {0,1}), ({1,2}, {0,1,2}), ({2}, {0,2})] {{0}} = false ∧
      ({1} : Finset (Fin 3)) ⊂ {1,2} := by
  decide +kernel

/-- Wrong endpoint: the obtuse step is free and the run ends at the α table, so the certificate is
rejected for the Čech table, for the α table with the long edge kept, and for the table without
the vertex `{2}`. -/
theorem checkSteps_triangle_wrong_endpoint :
    checkSteps triangle [({0,1}, {0,1,2})] triangle = false ∧
      checkSteps triangle [({0,1}, {0,1,2})] (insert {0,1} alphaTable) = false ∧
      checkSteps triangle [({0,1}, {0,1,2})] (alphaTable.erase {2}) = false ∧
      runSteps triangle [({0,1}, {0,1,2})] = some alphaTable := by
  decide +kernel

/-- Retention: from the Čech table the empty certificate reaches only the Čech table itself,
not the α table. -/
theorem checkSteps_triangle_nil :
    checkSteps triangle [] triangle = true ∧ checkSteps triangle [] alphaTable = false := by
  decide +kernel

/-- Repeated step: after the obtuse step, the same step is rejected, because its faces have
been erased. -/
theorem checkSteps_triangle_repeated :
    checkSteps triangle [({0,1}, {0,1,2}), ({0,1}, {0,1,2})] alphaTable = false ∧
      ({0,1} : Finset (Fin 3)) ∉ collapseTable triangle {0,1} {0,1,2} := by
  decide +kernel

/-- An accepted certificate gives a collapse of the actual full tetrahedron `⊤` onto the
complex with the single face `{0}`. -/
theorem top_collapsesTo_vertex :
    CollapsesTo (⊤ : PreAbstractSimplicialComplex (Fin 4))
      (FiniteComplex.toPre ⟨{{0}}, by decide, by decide⟩) := by
  refine collapsesTo_of_checkSteps (F := tetrahedron) (T := {{0}}) (fun s => ?_)
    (fun _ => Iff.rfl) checkSteps_tetrahedron_vertex
  change s.Nonempty ↔ s ∈ tetrahedron
  rw [tetrahedron, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
  simp

end TDA.Simplicial.CollapseCertificateExamples
