import TDA.Persistence.SublevelDiagramTransport
import TDA.Filtration.FilterFunctionMap
import TDA.Persistence.DiagramLaws

set_option autoImplicit false

/-!
# Reparametrizing persistence diagrams along order embeddings

An order embedding `φ : α ↪o β` maps every occurrence `(b, d)` of a diagram to
`(φ b, WithTop.map φ d)`: births and finite deaths are mapped and the essential death `⊤`
is fixed. Injectivity of `φ` keeps every mapped occurrence off the diagonal, and strict
monotonicity preserves positivity. The merged attained-grade transport theorem identifies
the actual diagram of a reparametrized filter with the reparametrized actual diagram,
in every degree and over every field.

These are library extensions proved from the merged definitions. Monotone non-injective
maps, which can move bars onto the diagonal, are outside this API.
-/

universe u v w z

namespace TDA.Persistence

variable {α : Type v} {β : Type w} {γ : Type z}
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Map births and finite deaths along an order embedding, fixing the essential death. -/
def Diagram.map (D : Diagram α) (φ : α ↪o β) : Diagram β where
  points := D.points.map (fun p => (φ p.1, WithTop.map φ p.2))
  offDiagonal := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    intro heq
    apply D.offDiagonal q hq
    apply WithTop.map_injective φ.injective
    simpa only [WithTop.map_coe] using heq

theorem Diagram.map_points (D : Diagram α) (φ : α ↪o β) :
    (D.map φ).points = D.points.map (fun p => (φ p.1, WithTop.map φ p.2)) := rfl

/-- Strictly increasing maps preserve positivity of every occurrence. -/
theorem Diagram.IsPositive.map {D : Diagram α} (hD : D.IsPositive) (φ : α ↪o β) :
    (D.map φ).IsPositive := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  have h := hD q hq
  obtain ⟨b, d⟩ := q
  cases d with
  | top => exact WithTop.coe_lt_top _
  | coe d =>
    change ((φ b : β) : WithTop β) < ((φ d : β) : WithTop β)
    exact WithTop.coe_lt_coe.2 (φ.lt_iff_lt.2 (WithTop.coe_lt_coe.1 h))

/-- The finite part maps coordinatewise. -/
theorem finitePart_map_points (D : Diagram α) (φ : α ↪o β) :
    finitePart (D.map φ).points = (finitePart D.points).map (fun p => (φ p.1, φ p.2)) := by
  rw [Diagram.map_points]
  simp only [finitePart, Multiset.filterMap_map, Multiset.map_filterMap]
  apply congrArg (fun g : (α × WithTop α) → Option (β × β) => D.points.filterMap g)
  funext p
  obtain ⟨b, d⟩ := p
  cases d <;> rfl

/-- The essential part maps by its births. -/
theorem essentialPart_map_points (D : Diagram α) (φ : α ↪o β) :
    essentialPart (D.map φ).points = (essentialPart D.points).map φ := by
  rw [Diagram.map_points]
  simp only [essentialPart, Multiset.filterMap_map, Multiset.map_filterMap]
  apply congrArg (fun g : (α × WithTop α) → Option β => D.points.filterMap g)
  funext p
  obtain ⟨b, d⟩ := p
  cases d <;> rfl

/-- Mapping along the identity embedding does nothing. -/
theorem Diagram.map_refl (D : Diagram α) : D.map (RelEmbedding.refl (· ≤ ·)) = D := by
  apply Diagram.ext
  rw [Diagram.map_points]
  have h : (fun p : α × WithTop α =>
      ((RelEmbedding.refl (· ≤ ·) : α ↪o α) p.1,
        WithTop.map (RelEmbedding.refl (· ≤ ·) : α ↪o α) p.2)) = id := by
    funext p
    obtain ⟨b, d⟩ := p
    cases d <;> rfl
  rw [h, Multiset.map_id]

/-- Successive diagram maps compose. -/
theorem Diagram.map_map (D : Diagram α) (φ : α ↪o β) (ψ : β ↪o γ) :
    (D.map φ).map ψ = D.map (φ.trans ψ) := by
  apply Diagram.ext
  rw [Diagram.map_points, Diagram.map_points, Diagram.map_points, Multiset.map_map]
  congr 1
  funext p
  obtain ⟨b, d⟩ := p
  cases d <;> rfl

/-- The actual diagram of a reparametrized filter is the reparametrized actual diagram. -/
theorem dgm_map {V : Type u} [LinearOrder V] (k : Type u) [Field k]
    {K : PreAbstractSimplicialComplex V} [Fintype (TDA.Simplicial.TotalFace K)]
    (f : TDA.Filtration.FilterFunction K α) (φ : α ↪o β) (n : ℕ) :
    dgm k (f.map φ) n = (dgm k f n).map φ :=
  Diagram.ext (dgm_points_map_of_strictMonoOn k f (f.map φ) φ
    (φ.strictMono.strictMonoOn _) (fun _ => rfl) n)

end TDA.Persistence
