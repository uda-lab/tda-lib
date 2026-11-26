import TDA.Mapper.RefinementHomologyDomainMap

set_option autoImplicit false

/-!
# Mapper diagrams without supplied component orders

The step diagram `stepMapperDiagram` and the capped centred diagram `cappedCentredDiagram` take
one linear order per stage on the component indices of the pulled-back cover; the orders orient
the simplices of the Mapper complexes.  A homeomorphism `e : X ≃ₜ X'` with `f' ∘ e = f` induces
an isomorphism of the Mapper homology modules of `f` and `f'` for independent orders on the two
sides, so the two step diagrams are equal (`stepMapperDiagram_eq_of_homeomorph`,
`cappedCentredDiagram_eq_of_homeomorph`).  For the identity of `X` this gives equality of the
diagrams of `f` for any two families of orders.

`cappedCentredDiagramOrderFree` is the capped centred diagram for the orders chosen classically
(the well-ordering `WellOrderingRel`).  It takes no order instance and equals
`cappedCentredDiagram` for every supplied family of orders (`cappedCentredDiagramOrderFree_eq`).
The perturbation bound, its graph-PL form and its uniform-grid form are stated for it.
-/

namespace TDA.Mapper

open CategoryTheory
open TDA.Topology
open TDA.Simplicial
open TDA.Persistence
open TDA.Persistence.FiniteConstructible

noncomputable section

universe u v

variable {X X' : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace X']
  [TopologicalSpace Y]

section Step

variable (k : Type u) [Field k] {f : C(X, Y)} {f' : C(X', Y)} (e : X ≃ₜ X')
  (he : ∀ x, f' (e x) = f x) {m : ℕ} (c : Fin m ↪o ℝ) {Index : Fin (m + 1) → Type u}
  (cover : (i : Fin (m + 1)) → Index i → Set Y)
  [∀ i, LinearOrder (ComponentIndex f (cover i))]
  [∀ i, LinearOrder (ComponentIndex f' (cover i))]
  (r : ∀ {i j : Fin (m + 1)}, i ≤ j → Refinement (cover i) (cover j)) (n : ℕ)
  [∀ i, Finite (Face (mapper f (cover i)) n)] [∀ i, Finite (Face (mapper f' (cover i)) n)]

include e he in
/-- Homeomorphic domains over `Y` have equal step diagrams, for independent component orders on
the two domains. -/
theorem stepMapperDiagram_eq_of_homeomorph :
    stepMapperDiagram k f c cover r n = stepMapperDiagram k f' c cover r n := by
  rw [stepMapperDiagram_eq_ofIndexBars_succ, stepMapperDiagram_eq_ofIndexBars_succ]
  exact congrArg (ofIndexBars c c.strictMono)
    (rankBarcode_eq_of_iso (mapperHomologyPModuleIso k e he (fun j : Fin m => cover j.succ)
      (fun h => r (Fin.succ_le_succ_iff.mpr h)) n))

end Step

section Capped

variable (k : Type u) [Field k] {W : Type u} {f : C(X, ℝ)} {f' : C(X', ℝ)} (e : X ≃ₜ X')
  (he : ∀ x, f' (e x) = f x) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin m ↪o ℝ) (n : ℕ)
  [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
  [∀ i, LinearOrder (ComponentIndex f' fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
  [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
  [∀ i, Finite (Face (mapper f' fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]

include e he in
/-- Homeomorphic domains over `ℝ` have equal capped centred diagrams, for independent
component orders on the two domains. -/
theorem cappedCentredDiagram_eq_of_homeomorph :
    cappedCentredDiagram k f a s ℓ c n = cappedCentredDiagram k f' a s ℓ c n :=
  stepMapperDiagram_eq_of_homeomorph k e he c _ _ n

end Capped

section CappedCongr

variable (k : Type u) [Field k] {W : Type u} {f : C(X, ℝ)} {f' : C(X', ℝ)} (e : X ≃ₜ X')
  (he : ∀ x, f' (e x) = f x) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin m ↪o ℝ) (n : ℕ)
  [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
  [∀ i, Finite (Face (mapper f' fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]

include e he in
/-- `cappedCentredDiagram_eq_of_homeomorph` with the two families of component orders as
explicit arguments. -/
theorem cappedCentredDiagram_congr
    (o : ∀ i, LinearOrder (ComponentIndex f fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ)))
    (o' : ∀ i, LinearOrder (ComponentIndex f' fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ))) :
    @cappedCentredDiagram k _ X _ W f a s ℓ m c n o _ =
      @cappedCentredDiagram k _ X' _ W f' a s ℓ m c n o' _ :=
  cappedCentredDiagram_eq_of_homeomorph k e he a s ℓ c n

end CappedCongr

section OrderFree

variable (k : Type u) [Field k] {W : Type u}

/-- The capped centred diagram of `f` with the component orders chosen classically (the
well-ordering `WellOrderingRel`).  It takes no order instance.  By
`cappedCentredDiagramOrderFree_eq` it equals `cappedCentredDiagram` for every supplied family of
orders. -/
def cappedCentredDiagramOrderFree (f : C(X, ℝ)) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ} (c : Fin m ↪o ℝ)
    (n : ℕ)
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)] :
    Diagram ℝ :=
  letI : ∀ i, LinearOrder (ComponentIndex f fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ)) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  cappedCentredDiagram k f a s ℓ c n

/-- The order-free capped centred diagram equals the diagram of any supplied component
orders. -/
theorem cappedCentredDiagramOrderFree_eq (f : C(X, ℝ)) (a s : ℝ) (ℓ : W → ℤ) {m : ℕ}
    (c : Fin m ↪o ℝ) (n : ℕ)
    [∀ i, LinearOrder (ComponentIndex f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ))]
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)] :
    cappedCentredDiagramOrderFree k f a s ℓ c n = cappedCentredDiagram k f a s ℓ c n := by
  have he : ∀ x, f (Homeomorph.refl X x) = f x := fun _ => rfl
  exact cappedCentredDiagram_congr k (Homeomorph.refl X) he a s ℓ c n
    (fun _ => IsWellOrder.linearOrder WellOrderingRel) inferInstance

variable (a s : ℝ) (ℓ : W → ℤ) (n : ℕ)

/-- **Perturbation bound, order-free.** If `|f x - g x| ≤ δ` for every `x` and consecutive radii
of the grid `c` differ by at most `μ`, then the order-free capped centred diagrams of `f` and
`g` on `c` are at bottleneck distance at most `δ + μ`. -/
theorem bottleneck_cappedCentredDiagramOrderFree_le {f g : C(X, ℝ)} {m : ℕ} {c : Fin m ↪o ℝ}
    [∀ i, Finite (Face (mapper f fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    [∀ i, Finite (Face (mapper g fun w => (cappedCentredCover a s ℓ c i w : Set ℝ)) n)]
    {δ μ : NNReal} (hfg : ∀ x, |f x - g x| ≤ δ)
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) :
    bottleneck (cappedCentredDiagramOrderFree k f a s ℓ c n)
      (cappedCentredDiagramOrderFree k g a s ℓ c n) ≤ (δ : ENNReal) + μ := by
  let : ∀ i, LinearOrder (ComponentIndex f fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ)) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  let : ∀ i, LinearOrder (ComponentIndex g fun w =>
      (cappedCentredCover a s ℓ c i w : Set ℝ)) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  exact bottleneck_cappedCentredDiagram_le k a s ℓ n hfg hgap

end OrderFree

section GraphPL

open TDA.Reeb

variable (k : Type u) [Field k] {V : Type u} [Finite V] (G : SimpleGraph V) {W : Type u}
  [Finite W] (a s : ℝ) (ℓ : W → ℤ) (n : ℕ) {h₁ h₂ : V → ℝ} {ε : NNReal}

/-- **Graph-PL vertex heights, order-free.** For vertex heights within `ε` at every vertex of a
finite graph, a finite label window and a grid of mesh at most `μ`, the order-free capped centred
diagrams of the two piecewise-linear heights are at bottleneck distance at most `ε + μ`. -/
theorem bottleneck_cappedCentredDiagramOrderFree_plHeight_le (hh : ∀ v, |h₁ v - h₂ v| ≤ ε)
    {m : ℕ} {c : Fin m ↪o ℝ} {μ : NNReal}
    (hgap : ∀ i j : Fin m, j.val = i.val + 1 → c j ≤ c i + μ) :
    bottleneck (cappedCentredDiagramOrderFree k (GraphPL.plHeight G h₁) a s ℓ c n)
        (cappedCentredDiagramOrderFree k (GraphPL.plHeight G h₂) a s ℓ c n) ≤
      (ε : ENNReal) + μ :=
  bottleneck_cappedCentredDiagramOrderFree_le k a s ℓ n (GraphPL.abs_plHeight_sub_le G hh)
    hgap

/-- **Graph-PL vertex heights on a uniform grid, order-free.** For vertex heights within
`ε = p * h` at every vertex of a finite graph and a finite label window, the order-free capped
centred diagrams of the two piecewise-linear heights on the uniform grid of spacing `h` are at
bottleneck distance at most `ε`. -/
theorem bottleneck_cappedCentredDiagramOrderFree_plHeight_uniformGrid_le
    (hh : ∀ v, |h₁ v - h₂ v| ≤ ε) (x₀ h : ℝ) (hpos : 0 < h) (m : ℕ) (p : ℕ)
    (hε : (ε : ℝ) = p * h) :
    bottleneck
        (cappedCentredDiagramOrderFree k (GraphPL.plHeight G h₁) a s ℓ
          (uniformGrid x₀ h hpos m) n)
        (cappedCentredDiagramOrderFree k (GraphPL.plHeight G h₂) a s ℓ
          (uniformGrid x₀ h hpos m) n) ≤
      ε := by
  let : ∀ i, LinearOrder (ComponentIndex (GraphPL.plHeight G h₁) fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hpos m) i w : Set ℝ)) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  let : ∀ i, LinearOrder (ComponentIndex (GraphPL.plHeight G h₂) fun w =>
      (cappedCentredCover a s ℓ (uniformGrid x₀ h hpos m) i w : Set ℝ)) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  exact bottleneck_cappedCentredDiagram_plHeight_uniformGrid_le k G a s ℓ n hh x₀ h hpos m p
    hε

end GraphPL

end

end TDA.Mapper
