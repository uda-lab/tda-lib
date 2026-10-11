import TDA.Filtration.CompatibleOrderTransfer

set_option autoImplicit false

/-!
# Fixtures for compatible-order transfer

Private examples exercise empty actual-face types, a deliberately noncanonical tied edge
enumeration, cross-codomain ordering equivalence, direct transfer without ordering equivalence,
and a grade reversal that fails monotonicity along the supplied enumeration. The finite list
checks demonstrate that transfer preserves the supplied order.
-/

namespace TDA.Filtration.CompatibleOrderTransferExamples

open TDA.Filtration TDA.Simplicial TDA.Simplicial.FiniteComplex

universe z
private instance emptyFaceIsEmpty (V : Type z) :
    IsEmpty (TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
  ⟨fun s => ((mem_bot_iff s.val).mp s.property).elim⟩
private instance emptyFaces (V : Type z) :
    Fintype (TotalFace (⊥ : PreAbstractSimplicialComplex V)) :=
  Fintype.ofIsEmpty
private theorem emptyCard (V : Type z) :
    Fintype.card (TotalFace (⊥ : PreAbstractSimplicialComplex V)) = 0 :=
  Fintype.card_ofIsEmpty
private instance emptyIndexIsEmpty (V : Type z) :
    IsEmpty (Fin (Fintype.card (TotalFace (⊥ : PreAbstractSimplicialComplex V)))) := by
  rw [emptyCard V]
  infer_instance

private def emptyFilter (V : Type z) (γ : Type) [LinearOrder γ] :
    FilterFunction (⊥ : PreAbstractSimplicialComplex V) γ where
  value := fun s => ((mem_bot_iff s.val).mp s.property).elim
  mono := by
    intro s t _
    exact ((mem_bot_iff s.val).mp s.property).elim

private def emptyEnum (V : Type z) :
    Fin (Fintype.card (TotalFace (⊥ : PreAbstractSimplicialComplex V))) ≃
      TotalFace (⊥ : PreAbstractSimplicialComplex V) :=
  Equiv.equivOfIsEmpty _ _

private def emptyOrder (V : Type z) : CompatibleOrder (emptyFilter V Unit) where
  enum := emptyEnum V
  face_lt := by intro i; exact (isEmptyElim i)
  monotone := by intro i; exact (isEmptyElim i)

private theorem emptyEquiv (V : Type z) :
    OrderingEquivalent (emptyFilter V Unit) (emptyFilter V Empty) := by
  intro s
  exact (isEmptyElim s)

private theorem emptyTransfer0 :
    ((emptyOrder (Fin 0)).transferOfOrderingEquivalent (emptyEquiv (Fin 0))).enum =
      (emptyOrder (Fin 0)).enum := rfl
private theorem emptyTransfer2 :
    ((emptyOrder (Fin 2)).transferOfOrderingEquivalent (emptyEquiv (Fin 2))).enum =
      (emptyOrder (Fin 2)).enum := rfl

private def edge2 : FiniteComplex 2 where
  faces := {{0}, {1}, {0, 1}}
  nonempty := by decide
  downClosed := by decide

private def v0 : TotalFace edge2.toPre := ⟨{0}, by decide⟩
private def v1 : TotalFace edge2.toPre := ⟨{1}, by decide⟩
private def edge : TotalFace edge2.toPre := ⟨{0, 1}, by decide⟩

private theorem edgeCard : Fintype.card (TotalFace edge2.toPre) = 3 := by decide
private def baseEnum : Fin 3 ≃ TotalFace edge2.toPre where
  toFun := fun i => ⟨if i = 0 then {1} else if i = 1 then {0} else {0, 1},
    by fin_cases i <;> decide⟩
  invFun := fun s => if s.val = ({1} : Finset (Fin 2)) then 0
    else if s.val = {0} then 1 else 2
  left_inv := by decide
  right_inv := by decide
private def suppliedEnum :
    Fin (Fintype.card (TotalFace edge2.toPre)) ≃ TotalFace edge2.toPre :=
  (Fin.castOrderIso edgeCard).toEquiv.trans baseEnum
private theorem baseFaceLt : ∀ i j : Fin 3,
    (baseEnum i).val ⊂ (baseEnum j).val → i < j := by decide

private def constantNat : FilterFunction edge2.toPre ℕ where
  value := fun _ => 0
  mono := by intros; exact le_rfl
private def constantInt : FilterFunction edge2.toPre ℤ where
  value := fun _ => 7
  mono := by intros; exact le_rfl

private def suppliedOrder : CompatibleOrder constantNat where
  enum := suppliedEnum
  face_lt := by
    intro i j h
    exact (Fin.castOrderIso edgeCard).lt_iff_lt.mp
      (baseFaceLt _ _ h)
  monotone := by intro i j _; exact le_rfl

private theorem constantEquiv : OrderingEquivalent constantNat constantInt := by
  intro s t
  simp [constantNat, constantInt]
private theorem tiedTransfer :
    (suppliedOrder.transferOfOrderingEquivalent constantEquiv).enum = suppliedEnum := rfl
private theorem suppliedFaces :
    (suppliedEnum (Fin.cast edgeCard.symm 0)).val = ({1} : Finset (Fin 2)) ∧
    (suppliedEnum (Fin.cast edgeCard.symm 1)).val = ({0} : Finset (Fin 2)) ∧
    (suppliedEnum (Fin.cast edgeCard.symm 2)).val = ({0, 1} : Finset (Fin 2)) := by decide
private theorem tiedFaces :
    ((suppliedOrder.transferOfOrderingEquivalent constantEquiv).enum (Fin.cast edgeCard.symm 0)).val =
      ({1} : Finset (Fin 2)) ∧
    ((suppliedOrder.transferOfOrderingEquivalent constantEquiv).enum (Fin.cast edgeCard.symm 1)).val =
      ({0} : Finset (Fin 2)) ∧
    ((suppliedOrder.transferOfOrderingEquivalent constantEquiv).enum (Fin.cast edgeCard.symm 2)).val =
      ({0, 1} : Finset (Fin 2)) := suppliedFaces
private theorem tiedFaceLt : ∀ i j,
    ((suppliedOrder.transferOfOrderingEquivalent constantEquiv).enum i).val ⊂
      ((suppliedOrder.transferOfOrderingEquivalent constantEquiv).enum j).val → i < j :=
  (suppliedOrder.transferOfOrderingEquivalent constantEquiv).face_lt

private def patternNat : FilterFunction edge2.toPre ℕ where
  value := fun s => if s.val = ({0, 1} : Finset (Fin 2)) then 1 else 0
  mono := by decide
private def patternInt : FilterFunction edge2.toPre ℤ where
  value := fun s => if s.val = ({0, 1} : Finset (Fin 2)) then 3 else 1
  mono := by decide
private theorem basePatternMono : Monotone (patternNat.value ∘ baseEnum) := by decide
private def patternOrder : CompatibleOrder patternNat where
  enum := suppliedEnum
  face_lt := suppliedOrder.face_lt
  monotone := by
    intro i j hij
    exact basePatternMono ((Fin.castOrderIso edgeCard).monotone hij)
private theorem patternEquiv : OrderingEquivalent patternNat patternInt := by
  intro s t
  dsimp [patternNat, patternInt]
  split_ifs <;> omega
private theorem patternValues :
    patternNat.value v1 = 0 ∧ patternNat.value v0 = 0 ∧
    patternNat.value edge = 1 ∧ patternInt.value v1 = 1 ∧
    patternInt.value v0 = 1 ∧ patternInt.value edge = 3 := by decide
private theorem patternTransferredMono :
    Monotone (patternInt.value ∘
      (patternOrder.transferOfOrderingEquivalent patternEquiv).enum) :=
  (patternOrder.transferOfOrderingEquivalent patternEquiv).monotone
private theorem patternEnum :
    (patternOrder.transferOfOrderingEquivalent patternEquiv).enum = suppliedEnum := rfl

private def splitForward : FilterFunction edge2.toPre ℤ where
  value := fun s => if s.val = ({0, 1} : Finset (Fin 2)) then 2
    else if s.val = {0} then 1 else 0
  mono := by decide
private theorem baseSplitForwardMono : Monotone (splitForward.value ∘ baseEnum) := by decide
private theorem splitForwardMono :
    Monotone (splitForward.value ∘ suppliedOrder.enum) := by
  intro i j hij
  exact baseSplitForwardMono ((Fin.castOrderIso edgeCard).monotone hij)
private theorem splitForwardNotEquiv :
    ¬ OrderingEquivalent constantNat splitForward := by
  intro h
  have hf : splitForward.value v0 ≤ splitForward.value v1 :=
    (h v0 v1).mp (by decide)
  exact (by decide : ¬ splitForward.value v0 ≤ splitForward.value v1) hf
private def directTransfer : CompatibleOrder splitForward :=
  suppliedOrder.transfer splitForwardMono
private theorem directEnum : directTransfer.enum = suppliedEnum := rfl
private theorem directValues :
    splitForward.value v1 = 0 ∧ splitForward.value v0 = 1 ∧
    splitForward.value edge = 2 := by decide

private def reversed : FilterFunction edge2.toPre ℤ where
  value := fun s => if s.val = ({0, 1} : Finset (Fin 2)) then 2
    else if s.val = {1} then 1 else 0
  mono := by decide
private theorem reversedValues :
    reversed.value v1 = 1 ∧ reversed.value v0 = 0 ∧
    reversed.value edge = 2 := by decide
private theorem reversedNotMono :
    ¬ Monotone (reversed.value ∘ suppliedOrder.enum) := by
  intro h
  have hf : reversed.value (suppliedOrder.enum (Fin.cast edgeCard.symm 0)) ≤
      reversed.value (suppliedOrder.enum (Fin.cast edgeCard.symm 1)) :=
    h (by simp)
  exact (by decide : ¬ reversed.value (suppliedOrder.enum (Fin.cast edgeCard.symm 0)) ≤
      reversed.value (suppliedOrder.enum (Fin.cast edgeCard.symm 1))) hf

private def faceList (e : Fin (Fintype.card (TotalFace edge2.toPre)) ≃
    TotalFace edge2.toPre) : List (Finset (Fin 2)) :=
  List.ofFn (fun i => (e i).val)
#eval faceList suppliedEnum
#eval faceList (suppliedOrder.transferOfOrderingEquivalent constantEquiv).enum
#eval faceList (patternOrder.transferOfOrderingEquivalent patternEquiv).enum
#eval faceList directTransfer.enum

#print axioms emptyEquiv
#print axioms emptyTransfer0
#print axioms emptyTransfer2
#print axioms suppliedFaces
#print axioms tiedFaces
#print axioms tiedFaceLt
#print axioms patternEquiv
#print axioms patternValues
#print axioms patternTransferredMono
#print axioms splitForwardMono
#print axioms splitForwardNotEquiv
#print axioms directValues
#print axioms reversedValues
#print axioms reversedNotMono
#print axioms directTransfer
#print axioms emptyFaceIsEmpty
#print axioms emptyFaces
#print axioms emptyCard
#print axioms emptyIndexIsEmpty
#print axioms emptyFilter
#print axioms emptyEnum
#print axioms emptyOrder
#print axioms edge2
#print axioms v0
#print axioms v1
#print axioms edge
#print axioms edgeCard
#print axioms baseEnum
#print axioms suppliedEnum
#print axioms baseFaceLt
#print axioms constantNat
#print axioms constantInt
#print axioms suppliedOrder
#print axioms constantEquiv
#print axioms tiedTransfer
#print axioms patternNat
#print axioms patternInt
#print axioms basePatternMono
#print axioms patternOrder
#print axioms patternEnum
#print axioms splitForward
#print axioms baseSplitForwardMono
#print axioms directEnum
#print axioms reversed
#print axioms faceList

end TDA.Filtration.CompatibleOrderTransferExamples
