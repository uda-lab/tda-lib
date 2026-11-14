import TDA.Reeb.GeometricThickening
import TDA.Topology.QuotientProduct

/-!
# Morphisms of cylinder presentations on a common grid

A morphism `φ : P.Hom Q` of cylinder presentations over the same number of levels consists of
continuous maps `V i → V' i` on the vertex pieces and `E e → E' e` on the edge pieces commuting
with both endpoint maps. These are the attachment-diagram maps of the proof of de Silva–Munch–Patel,
Theorem 4.27, restricted to diagrams over one fixed grid; maps that change the grid or move the
cylinder parameter are not morphisms here.

* Realization. On a fixed list of levels `S`, `φ.realize S` is the continuous map of realizations
  that is `φ.vertex i` on vertex points and `φ.edge e × id` on cylinder points (`realize_ofVertex`,
  `realize_ofCylinder`, `realize_ofStrip`). It is obtained from the universal property through
  `Hom.compatibleMaps`, preserves height (`height_realize`) and is functorial (`realize_id`,
  `realize_comp`). In universe `0` it is a morphism of the real slice (`toOverHom`).
* Finite data. A map of finite data is a morphism of the discrete presentations
  (`FiniteReebData.Hom.toPresentationHom`), realized by the existing `realizeHom`
  (`realize_toPresentationHom`).
* Pieces times a locally compact space. `quotMk × id_I` is a quotient map for every locally
  compact `I` (`isQuotientMap_prodMap_quotMk`), with fibres `nf x = nf x'` and equal second
  coordinates (`prodMap_quotMk_eq_iff`). For the band `I = [-ε, ε]` (`isQuotientMap_rawBandMap`)
  this says that `X × [-ε, ε]` is the quotient of the thickened raw pieces
  `Σ V i × [-ε, ε] ⊕ Σ E e × [a e, a (e+1)] × [-ε, ε]` by the endpoint identifications. Together
  with `lift` and `hom_ext` it is the form in which the colimit description of the thickening is
  used. No piece is assumed Hausdorff, compact or locally path-connected.

See `docs/math/reeb-thickening-constructible.md`.
-/

open Set Topology CategoryTheory
open scoped NNReal

universe u v w w'

namespace TDA.Reeb

noncomputable section

namespace CylinderPresentation

variable {n : ℕ}

/-- A morphism of cylinder presentations on a common grid: continuous maps on all vertex and
edge pieces commuting with both endpoint maps. -/
@[ext]
structure Hom (P : CylinderPresentation.{u} n) (Q : CylinderPresentation.{v} n) where
  /-- The map on each vertex piece. -/
  vertex : ∀ i, C(P.V i, Q.V i)
  /-- The map on each edge piece. -/
  edge : ∀ e, C(P.E e, Q.E e)
  /-- Compatibility with the left endpoint maps. -/
  left_comm : ∀ e y, Q.left e (edge e y) = vertex e.castSucc (P.left e y)
  /-- Compatibility with the right endpoint maps. -/
  right_comm : ∀ e y, Q.right e (edge e y) = vertex e.succ (P.right e y)

namespace Hom

variable {P : CylinderPresentation.{u} n} {Q : CylinderPresentation.{v} n}
  {R : CylinderPresentation.{w} n}

/-- The identity morphism. -/
def id (P : CylinderPresentation.{u} n) : P.Hom P :=
  ⟨fun _ => ContinuousMap.id _, fun _ => ContinuousMap.id _, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Composition of morphisms, `φ` first. -/
def comp (φ : P.Hom Q) (ψ : Q.Hom R) : P.Hom R where
  vertex i := (ψ.vertex i).comp (φ.vertex i)
  edge e := (ψ.edge e).comp (φ.edge e)
  left_comm e y := (ψ.left_comm e _).trans (congrArg _ (φ.left_comm e y))
  right_comm e y := (ψ.right_comm e _).trans (congrArg _ (φ.right_comm e y))

@[simp] theorem id_vertex (P : CylinderPresentation.{u} n) (i : Fin (n + 1)) :
    (Hom.id P).vertex i = ContinuousMap.id _ := rfl

@[simp] theorem id_edge (P : CylinderPresentation.{u} n) (e : Fin n) :
    (Hom.id P).edge e = ContinuousMap.id _ := rfl

@[simp] theorem comp_vertex (φ : P.Hom Q) (ψ : Q.Hom R) (i : Fin (n + 1)) :
    (φ.comp ψ).vertex i = (ψ.vertex i).comp (φ.vertex i) := rfl

@[simp] theorem comp_edge (φ : P.Hom Q) (ψ : Q.Hom R) (e : Fin n) :
    (φ.comp ψ).edge e = (ψ.edge e).comp (φ.edge e) := rfl

theorem id_comp (φ : P.Hom Q) : (Hom.id P).comp φ = φ := rfl

theorem comp_id (φ : P.Hom Q) : φ.comp (Hom.id Q) = φ := rfl

theorem comp_assoc {T : CylinderPresentation.{w'} n} (φ : P.Hom Q) (ψ : Q.Hom R) (χ : R.Hom T) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := rfl

variable (S : CriticalValues n)

/-- The compatible maps on the raw pieces of `P` given by a morphism: `ofVertex i ∘ φ.vertex i`
on vertex pieces and `ofCylinder e ∘ (φ.edge e × id)` on cylinders. -/
def compatibleMaps (φ : P.Hom Q) : P.CompatibleMaps S (Q.Realization S) where
  vertex i := ⟨fun v => Q.ofVertex S i (φ.vertex i v),
    (Q.continuous_ofVertex S i).comp (φ.vertex i).continuous⟩
  cylinder e := ⟨fun p => Q.ofCylinder S e (φ.edge e p.1, p.2),
    (Q.continuous_ofCylinder S e).comp (((φ.edge e).continuous.comp continuous_fst).prodMk
      continuous_snd)⟩
  segBot_eq e y := (Q.ofCylinder_segBot S e (φ.edge e y)).trans
    (congrArg (Q.ofVertex S e.castSucc) (φ.left_comm e y))
  segTop_eq e y := (Q.ofCylinder_segTop S e (φ.edge e y)).trans
    (congrArg (Q.ofVertex S e.succ) (φ.right_comm e y))

/-- The realization of a morphism on a fixed list of levels: `φ.vertex i` on vertex points and
`φ.edge e × id` on cylinder points. -/
def realize (φ : P.Hom Q) : C(P.Realization S, Q.Realization S) :=
  lift (φ.compatibleMaps S)

@[simp] theorem realize_ofVertex (φ : P.Hom Q) (i : Fin (n + 1)) (v : P.V i) :
    φ.realize S (P.ofVertex S i v) = Q.ofVertex S i (φ.vertex i v) := rfl

@[simp] theorem realize_ofCylinder (φ : P.Hom Q) (e : Fin n) (p : P.Cylinder S e) :
    φ.realize S (P.ofCylinder S e p) = Q.ofCylinder S e (φ.edge e p.1, p.2) := rfl

@[simp] theorem realize_ofStrip (φ : P.Hom Q) (e : Fin n) (p : P.E e × (S.K e : Set ℝ)) :
    φ.realize S (P.ofStrip S e p) = Q.ofStrip S e (φ.edge e p.1, p.2) := rfl

/-- The realization of a morphism preserves height. -/
@[simp] theorem height_realize (φ : P.Hom Q) (x : P.Realization S) :
    Q.height S (φ.realize S x) = P.height S x := by
  obtain ⟨r, rfl⟩ := P.quotMk_surjective S x
  rcases r with ⟨i, v⟩ | ⟨e, p⟩ <;> rfl

theorem height_comp_realize (φ : P.Hom Q) : (Q.height S).comp (φ.realize S) = P.height S :=
  ContinuousMap.ext (φ.height_realize S)

/-- The identity morphism realizes to the identity. -/
@[simp] theorem realize_id (P : CylinderPresentation.{u} n) :
    (Hom.id P).realize S = ContinuousMap.id _ :=
  hom_ext (fun _ _ => rfl) fun _ _ => rfl

/-- Realization preserves composition. -/
theorem realize_comp (φ : P.Hom Q) (ψ : Q.Hom R) :
    (φ.comp ψ).realize S = (ψ.realize S).comp (φ.realize S) :=
  hom_ext (fun _ _ => rfl) fun _ _ => rfl

/-- In universe `0`, the realization of a morphism as a morphism of the real slice. -/
def toOverHom {P Q : CylinderPresentation.{0} n} (φ : P.Hom Q) :
    Over.mk (TopCat.ofHom (P.height S)) ⟶ Over.mk (TopCat.ofHom (Q.height S)) :=
  Over.homMk (TopCat.ofHom (φ.realize S)) (by ext x; exact φ.height_realize S x)

@[simp] theorem toOverHom_left {P Q : CylinderPresentation.{0} n} (φ : P.Hom Q) :
    (φ.toOverHom S).left = TopCat.ofHom (φ.realize S) := rfl

theorem toOverHom_id (P : CylinderPresentation.{0} n) :
    (Hom.id P).toOverHom S = 𝟙 _ := by
  ext x
  exact DFunLike.congr_fun (realize_id S P) x

theorem toOverHom_comp {P Q R : CylinderPresentation.{0} n} (φ : P.Hom Q) (ψ : Q.Hom R) :
    (φ.comp ψ).toOverHom S = φ.toOverHom S ≫ ψ.toOverHom S := by
  ext x
  exact DFunLike.congr_fun (realize_comp S φ ψ) x

end Hom

/-! ### Finite data -/

/-- A map of finite data is a morphism of the discrete presentations. -/
def _root_.TDA.Reeb.FiniteReebData.Hom.toPresentationHom {D D' : FiniteReebData.{u} n}
    (φ : D.Hom D') : (ofFiniteData D).Hom (ofFiniteData D') where
  vertex i := ⟨φ.v i, continuous_of_discreteTopology⟩
  edge e := ⟨φ.e e, continuous_of_discreteTopology⟩
  left_comm := φ.left_comm
  right_comm := φ.right_comm

/-- The realization of a finite map as a presentation morphism is `realizeHom`. -/
theorem realize_toPresentationHom (S : CriticalValues n) {D D' : FiniteReebData.{u} n}
    (φ : D.Hom D') : φ.toPresentationHom.realize S = realizeHom S φ :=
  hom_ext (fun _ _ => rfl) fun _ _ => rfl

/-! ### Raw pieces times a locally compact space -/

variable (S : CriticalValues n) (P : CylinderPresentation.{u} n)

/-- The quotient map of a realization stays a quotient map after product with the identity of a
locally compact space. No piece is assumed Hausdorff. -/
theorem isQuotientMap_prodMap_quotMk (I : Type w) [TopologicalSpace I] [LocallyCompactSpace I] :
    IsQuotientMap (Prod.map (P.quotMk S) (_root_.id : I → I)) :=
  TDA.Topology.isQuotientMap_prodMap_id_left (P.isQuotientMap_quotMk S)

/-- The fibres of `quotMk × id`: equal normal forms and equal second coordinates. -/
theorem prodMap_quotMk_eq_iff {I : Type w} {x x' : P.Raw S × I} :
    Prod.map (P.quotMk S) _root_.id x = Prod.map (P.quotMk S) _root_.id x' ↔
      P.nf S x.1 = P.nf S x'.1 ∧ x.2 = x'.2 := by
  rw [Prod.ext_iff]
  exact and_congr (P.quotMk_eq_iff S) Iff.rfl

/-- The thickened realization `X × [-ε, ε]` is the quotient of the thickened raw pieces by the
endpoint identifications. -/
theorem isQuotientMap_rawBandMap (ε : ℝ≥0) :
    IsQuotientMap (Prod.map (P.quotMk S) _root_.id :
      P.Raw S × GeometricThickening.Band ε → P.Realization S × GeometricThickening.Band ε) :=
  P.isQuotientMap_prodMap_quotMk S _

end CylinderPresentation

end

end TDA.Reeb
