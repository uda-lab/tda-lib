import TDA.Filtration.OrderingEquivalent
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# Reparametrizing face-value filters along order embeddings

A filter function with values in `α` is reparametrized along an order embedding
`φ : α ↪o β` by composing its values with `φ`. Monotonicity is preserved, sublevels
correspond at every source threshold, and at every target threshold when `φ` is an order
isomorphism, and the original and reparametrized filters are ordering-equivalent. Positive
scaling of real filters is the special case `φ = OrderIso.mulLeft₀ c hc`.

These are library extensions proved from the merged definitions; no external theorem is
translated. Monotone non-injective and order-reversing maps are outside this API.
-/

universe u v w z

namespace TDA.Filtration.FilterFunction

open TDA.Simplicial

variable {V : Type u} {K : PreAbstractSimplicialComplex V}
variable {α : Type v} {β : Type w} {γ : Type z}
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

/-- Two filters with the same value on every face are equal. -/
@[ext] theorem ext {f g : FilterFunction K α} (h : ∀ s, f.value s = g.value s) : f = g := by
  cases f
  cases g
  congr
  funext s
  exact h s

/-- Reparametrize the values of a filter along an order embedding. -/
def map (f : FilterFunction K α) (φ : α ↪o β) : FilterFunction K β where
  value s := φ (f.value s)
  mono h := φ.monotone (f.mono h)

@[simp] theorem map_value (f : FilterFunction K α) (φ : α ↪o β) (s : TotalFace K) :
    (f.map φ).value s = φ (f.value s) := rfl

/-- The reparametrized sublevel at the image of a source threshold is the source sublevel. -/
theorem map_sublevel_apply (f : FilterFunction K α) (φ : α ↪o β) (r : α) :
    (f.map φ).sublevel (φ r) = f.sublevel r := by
  apply le_antisymm
  · rintro s ⟨hs, h⟩
    exact ⟨hs, φ.le_iff_le.1 h⟩
  · rintro s ⟨hs, h⟩
    exact ⟨hs, φ.le_iff_le.2 h⟩

/-- Along an order isomorphism every target threshold is the image of a source threshold. -/
theorem map_sublevel_orderIso (f : FilterFunction K α) (e : α ≃o β) (q : β) :
    (f.map e.toOrderEmbedding).sublevel q = f.sublevel (e.symm q) := by
  have h := map_sublevel_apply f e.toOrderEmbedding (e.symm q)
  simpa only [OrderIso.coe_toOrderEmbedding, OrderIso.apply_symm_apply] using h

/-- A filter and its reparametrization make exactly the same weak comparisons. -/
theorem orderingEquivalent_map (f : FilterFunction K α) (φ : α ↪o β) :
    OrderingEquivalent f (f.map φ) :=
  fun _ _ => φ.le_iff_le.symm

/-- Reparametrizing along the identity embedding does nothing. -/
theorem map_refl (f : FilterFunction K α) : f.map (RelEmbedding.refl (· ≤ ·)) = f := by
  ext s
  rfl

/-- Successive reparametrizations compose. -/
theorem map_map (f : FilterFunction K α) (φ : α ↪o β) (ψ : β ↪o γ) :
    (f.map φ).map ψ = f.map (φ.trans ψ) := by
  ext s
  rfl

/-- Multiply every face value of a real filter by a positive constant. -/
noncomputable def scale (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) : FilterFunction K ℝ :=
  f.map (OrderIso.mulLeft₀ c hc).toOrderEmbedding

@[simp] theorem scale_value (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c)
    (s : TotalFace K) : (f.scale c hc).value s = c * f.value s := rfl

/-- The scaled sublevel at `r` is the original sublevel at `c⁻¹ * r`. -/
theorem scale_sublevel (f : FilterFunction K ℝ) (c : ℝ) (hc : 0 < c) (r : ℝ) :
    (f.scale c hc).sublevel r = f.sublevel (c⁻¹ * r) := by
  rw [scale, map_sublevel_orderIso, OrderIso.mulLeft₀_symm, OrderIso.mulLeft₀_apply]

theorem scale_one (f : FilterFunction K ℝ) : f.scale 1 one_pos = f := by
  ext s
  simp

theorem scale_scale (f : FilterFunction K ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (f.scale a ha).scale b hb = f.scale (b * a) (mul_pos hb ha) := by
  ext s
  simp [mul_assoc]

end TDA.Filtration.FilterFunction
