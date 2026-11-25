import TDA.Topology.ConvexNerveInclusion

/-!
# Client statements of the last-vertex comparisons

Regression fixtures for #1148. Each statement is written as a client writes it: the file
opens no scope, declares no instance, and resolves the orders on the refined labels
`Vertex V n` and `Vertex (Finset I) n` by ordinary instance search, at a variable and at the
literal depth `1`. The apex-map comparison is applied with the client's own decidable
equality.
-/

namespace TDA.Topology.LastVertexClientExamples

open CategoryTheory TDA.Simplicial

section Labels

variable {I : Type} [Fintype I] [LinearOrder I] [Nonempty I]

/-- The iterated last vertex at a variable depth, stated by a client. -/
theorem iteratedLastVertex_isIso (K : PreAbstractSimplicialComplex I) (n k : ℕ) :
    IsIso (simplicialHomologyMap ℤ (SubdivisionRealization.iteratedLastVertex K n) k) :=
  SubdivisionRealization.isIso_iteratedLastVertex K ℤ k n

/-- The iterated last vertex at the literal depth one. -/
theorem iteratedLastVertex_one_isIso (K : PreAbstractSimplicialComplex I) (k : ℕ) :
    IsIso (simplicialHomologyMap ℤ (SubdivisionRealization.iteratedLastVertex K 1) k) :=
  SubdivisionRealization.isIso_iteratedLastVertex K ℤ k 1

/-- The flag last vertex at a variable depth, stated by a client. -/
theorem flagLastVertex_isIso (K : PreAbstractSimplicialComplex I) (n k : ℕ) :
    IsIso (simplicialHomologyMap ℤ (SubdivisionRealization.flagLastVertex K n) k) :=
  SubdivisionRealization.isIso_flagLastVertex K ℤ k n

/-- The flag last vertex at the literal depth one. -/
theorem flagLastVertex_one_isIso (K : PreAbstractSimplicialComplex I) (k : ℕ) :
    IsIso (simplicialHomologyMap ℤ (SubdivisionRealization.flagLastVertex K 1) k) :=
  SubdivisionRealization.isIso_flagLastVertex K ℤ k 1

/-- Both last-vertex maps of the filled triangle at depth one, over a concrete label type. -/
theorem triangle_lastVertex_one_isIso (k : ℕ) :
    IsIso (simplicialHomologyMap ℤ
      (SubdivisionRealization.iteratedLastVertex (⊤ : PreAbstractSimplicialComplex (Fin 3)) 1) k) ∧
    IsIso (simplicialHomologyMap ℤ
      (SubdivisionRealization.flagLastVertex (⊤ : PreAbstractSimplicialComplex (Fin 3)) 1) k) :=
  ⟨SubdivisionRealization.isIso_iteratedLastVertex _ ℤ k 1,
    SubdivisionRealization.isIso_flagLastVertex _ ℤ k 1⟩

/-- A further linear order on `Finset I` in the client's context does not change the order
on the labels of subdivided flags. -/
example [LinearOrder (Finset I)] (K : PreAbstractSimplicialComplex I) (k : ℕ) :
    IsIso (simplicialHomologyMap ℤ (SubdivisionRealization.flagLastVertex K 1) k) :=
  SubdivisionRealization.isIso_flagLastVertex K ℤ k 1

end Labels

section Labelling

variable {I : Type} [Fintype I] [LinearOrder I] [Nonempty I]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The signed labelling comparison at the literal depth one, stated by a client. -/
theorem labeling_lastVertex_one (U : I → Set E) (hc : ∀ i, Convex ℝ (U i)) (p : Finset I → E)
    (hp : ∀ A ∈ nerve U, ∀ i ∈ A, p A ∈ U i)
    (a : VertexMap (SubdivisionRealization.subdividedFlags (nerve U) 1) (nerve U))
    (ha : ∀ T ∈ SubdivisionRealization.subdividedFlags (nerve U) 1, ∀ v ∈ T, ∀ w ∈ T,
      SubdivisionRealization.vertexPosition p 1 w ∈ U (a v)) :
    Nonempty (Homotopy (simplicialChainMap ℤ a)
      (simplicialChainMap ℤ (SubdivisionRealization.flagLastVertex (nerve U) 1))) :=
  ConvexNerve.chainHomotopy_labeling_lastVertex U hc p hp 1 a ha ℤ

/-- The common subdivision comparison, stated by a client. -/
theorem common_chain_comparisons {C D : I → Set E} (ho : ∀ i, IsOpen (C i))
    (hC : ∀ i, Convex ℝ (C i)) (hD : ∀ i, Convex ℝ (D i))
    (h : ∀ i, C i ⊆ D i) (hu : (⋃ i, C i) = ⋃ i, D i) :
    let K := nerve C
    let L := nerve D
    let i : VertexMap K L := inclusionVertexMap (nerve_mono h)
    ∃ (n : ℕ) (a : VertexMap (SubdivisionRealization.subdividedFlags L n) K),
      let j : VertexMap (SubdivisionRealization.subdividedFlags K n)
          (SubdivisionRealization.subdividedFlags L n) :=
        inclusionVertexMap (SubdivisionRealization.complex_mono
          (SubdivisionRealization.subdivision_mono (nerve_mono h)) n)
      let aK := VertexMap.comp j a
      let aL := VertexMap.comp a i
      (∀ v, aK v = a v ∧ aL v = a v) ∧ VertexMap.comp j aL = VertexMap.comp aK i ∧
      ∀ (R : Type) [Ring R],
        Nonempty (Homotopy (simplicialChainMap R aK)
          (simplicialChainMap R (SubdivisionRealization.flagLastVertex K n))) ∧
        Nonempty (Homotopy (simplicialChainMap R aL)
          (simplicialChainMap R (SubdivisionRealization.flagLastVertex L n))) :=
  ConvexNerve.exists_common_chain_comparisons ho hC hD h hu

end Labelling

section Apex

variable {V I : Type} [Fintype V] [LinearOrder V] [Nonempty V] [DecidableEq I]
variable {Q : PreAbstractSimplicialComplex V} {N : PreAbstractSimplicialComplex I}

/-- The apex-map comparison with the client's own decidable equality on the target labels. -/
theorem contiguous_apexMap (f g : VertexMap Q N) (J : Finset V → Finset I)
    (j : Finset V → I) (hj : ∀ S ∈ Q, j S ∈ J S)
    (hanti : ∀ S ∈ Q, ∀ T ∈ Q, S ⊆ T → J T ⊆ J S)
    (hf : ∀ S ∈ Q, ∀ T ∈ Q, S ⊆ T → T.image f ∈ ConvexNerve.coneCarrier N (J S))
    (hg : ∀ S ∈ Q, ∀ T ∈ Q, S ⊆ T → T.image g ∈ ConvexNerve.coneCarrier N (J S)) :
    ∃ b : VertexMap (barycentricSubdivision Q) N,
      Contiguous (VertexMap.comp (lastVertexMap Q) f) b ∧
      Contiguous (VertexMap.comp (lastVertexMap Q) g) b :=
  ConvexNerve.exists_contiguous_apexMap f g J j hj hanti hf hg

end Apex

/-- The apex-map comparison on the subdivided flags at the literal depth one, whose labels
carry the flag order. -/
theorem contiguous_apexMap_flags_one {I : Type} [Fintype I] [LinearOrder I] [Nonempty I]
    {K : PreAbstractSimplicialComplex I} {N : PreAbstractSimplicialComplex I}
    (f g : VertexMap (SubdivisionRealization.subdividedFlags K 1) N)
    (J : Finset (SubdivisionRealization.Vertex (Finset I) 1) → Finset I)
    (j : Finset (SubdivisionRealization.Vertex (Finset I) 1) → I)
    (hj : ∀ S ∈ SubdivisionRealization.subdividedFlags K 1, j S ∈ J S)
    (hanti : ∀ S ∈ SubdivisionRealization.subdividedFlags K 1,
      ∀ T ∈ SubdivisionRealization.subdividedFlags K 1, S ⊆ T → J T ⊆ J S)
    (hf : ∀ S ∈ SubdivisionRealization.subdividedFlags K 1,
      ∀ T ∈ SubdivisionRealization.subdividedFlags K 1, S ⊆ T →
        T.image f ∈ ConvexNerve.coneCarrier N (J S))
    (hg : ∀ S ∈ SubdivisionRealization.subdividedFlags K 1,
      ∀ T ∈ SubdivisionRealization.subdividedFlags K 1, S ⊆ T →
        T.image g ∈ ConvexNerve.coneCarrier N (J S)) :
    ∃ b : VertexMap (barycentricSubdivision (SubdivisionRealization.subdividedFlags K 1)) N,
      Contiguous (VertexMap.comp (lastVertexMap (SubdivisionRealization.subdividedFlags K 1)) f) b ∧
      Contiguous (VertexMap.comp (lastVertexMap (SubdivisionRealization.subdividedFlags K 1)) g) b :=
  ConvexNerve.exists_contiguous_apexMap f g J j hj hanti hf hg

end TDA.Topology.LastVertexClientExamples
