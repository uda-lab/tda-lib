import TDA.Persistence.Diagram

universe u
namespace TDA.Persistence

def finitePart {α : Type u} [LinearOrder α]
    (s : Multiset (α × WithTop α)) : Multiset (α × α) :=
  s.filterMap fun p => match p.2 with
    | none => none
    | some d => some (p.1, d)

def essentialPart {α : Type u} [LinearOrder α]
    (s : Multiset (α × WithTop α)) : Multiset α :=
  s.filterMap fun p => match p.2 with
    | none => some p.1
    | some _ => none

private def finiteEmbed {α : Type u} [LinearOrder α] (p : α × α) : α × WithTop α :=
  (p.1, (p.2 : WithTop α))

private def essentialEmbed {α : Type u} [LinearOrder α] (b : α) : α × WithTop α :=
  (b, ⊤)

private theorem finitePart_add {α : Type u} [LinearOrder α]
    (s t : Multiset (α × WithTop α)) :
    finitePart (s + t) = finitePart s + finitePart t := by
  exact Multiset.filterMap_add _ _ _

private theorem essentialPart_add {α : Type u} [LinearOrder α]
    (s t : Multiset (α × WithTop α)) :
    essentialPart (s + t) = essentialPart s + essentialPart t := by
  exact Multiset.filterMap_add _ _ _

private theorem filterMap_none {β γ : Type*} (s : Multiset β) :
    s.filterMap (fun _ => (none : Option γ)) = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | @cons a s ih => simpa using ih

private theorem finitePart_finiteEmbed {α : Type u} [LinearOrder α]
    (s : Multiset (α × α)) : finitePart (s.map finiteEmbed) = s := by
  rw [finitePart, Multiset.filterMap_map]
  simpa only [finiteEmbed, Function.comp_def] using (Multiset.filterMap_some s)

private theorem finitePart_essentialEmbed {α : Type u} [LinearOrder α]
    (s : Multiset α) : finitePart (s.map essentialEmbed) = 0 := by
  rw [finitePart, Multiset.filterMap_map]
  simpa only [essentialEmbed, Function.comp_def] using (filterMap_none (γ := α × α) s)

private theorem essentialPart_finiteEmbed {α : Type u} [LinearOrder α]
    (s : Multiset (α × α)) : essentialPart (s.map finiteEmbed) = 0 := by
  rw [essentialPart, Multiset.filterMap_map]
  simpa only [finiteEmbed, Function.comp_def] using (filterMap_none (γ := α) s)

private theorem essentialPart_essentialEmbed {α : Type u} [LinearOrder α]
    (s : Multiset α) : essentialPart (s.map essentialEmbed) = s := by
  rw [essentialPart, Multiset.filterMap_map]
  simpa only [essentialEmbed, Function.comp_def] using (Multiset.filterMap_some s)

private theorem split_reconstruct {α : Type u} [LinearOrder α]
    (s : Multiset (α × WithTop α)) :
    (finitePart s).map finiteEmbed + (essentialPart s).map essentialEmbed = s := by
  induction s using Multiset.induction_on with
  | empty => simp [finitePart, essentialPart]
  | @cons p s ih =>
    obtain ⟨b, d⟩ := p
    cases d with
    | top =>
      simpa [finitePart, essentialPart, finiteEmbed, essentialEmbed,
        Multiset.map_cons, add_assoc, add_comm, add_left_comm] using ih
    | coe d =>
      simpa [finitePart, essentialPart, finiteEmbed, essentialEmbed,
        Multiset.map_cons, add_assoc, add_comm, add_left_comm] using ih

theorem finitePart_orderedQ {α : Type u} [LinearOrder α] (m n : ℕ)
    (z : (Fin m → α × α) × (Fin n → α)) :
    finitePart (orderedQ m n z).points =
      (Multiset.ofList (List.ofFn z.1)).filter (fun p => p.1 ≠ p.2) := by
  change finitePart (((Multiset.ofList (List.ofFn z.1)).filter
    (fun p => p.1 ≠ p.2)).map finiteEmbed +
    (Multiset.ofList (List.ofFn z.2)).map essentialEmbed) = _
  rw [finitePart_add, finitePart_finiteEmbed, finitePart_essentialEmbed, add_zero]

theorem essentialPart_orderedQ {α : Type u} [LinearOrder α] (m n : ℕ)
    (z : (Fin m → α × α) × (Fin n → α)) :
    essentialPart (orderedQ m n z).points =
      Multiset.ofList (List.ofFn z.2) := by
  change essentialPart (((Multiset.ofList (List.ofFn z.1)).filter
    (fun p => p.1 ≠ p.2)).map finiteEmbed +
    (Multiset.ofList (List.ofFn z.2)).map essentialEmbed) = _
  rw [essentialPart_add, essentialPart_finiteEmbed, essentialPart_essentialEmbed, zero_add]

private theorem finitePart_offDiagonal {α : Type u} [LinearOrder α] (D : Diagram α) :
    ∀ p ∈ finitePart D.points, p.1 ≠ p.2 := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := (Multiset.mem_filterMap _ _).mp hp
  obtain ⟨b, d⟩ := q
  cases d with
  | top => simp at hqp
  | coe d =>
    have hd := D.offDiagonal (b, (d : WithTop α)) hq
    simp at hqp
    subst p
    simpa using hd

private theorem finitePart_filter {α : Type u} [LinearOrder α] (D : Diagram α) :
    (finitePart D.points).filter (fun p => p.1 ≠ p.2) = finitePart D.points := by
  exact Multiset.filter_eq_self.mpr (finitePart_offDiagonal D)

theorem orderedQ_append {α : Type u} [LinearOrder α] (m n m' n' : ℕ)
    (z : (Fin m → α × α) × (Fin n → α))
    (w : (Fin m' → α × α) × (Fin n' → α)) :
    (orderedQ (m + m') (n + n')
      (Fin.append z.1 w.1, Fin.append z.2 w.2)).points =
      (orderedQ m n z).points + (orderedQ m' n' w).points := by
  simp only [orderedQ, List.ofFn_fin_append, ← Multiset.coe_add,
    Multiset.filter_add, Multiset.map_add]
  ac_rfl

theorem orderedQ_eq_iff {α : Type u} [LinearOrder α] (m n m' n' : ℕ)
    (z : (Fin m → α × α) × (Fin n → α))
    (w : (Fin m' → α × α) × (Fin n' → α)) :
    orderedQ m n z = orderedQ m' n' w ↔
      (Multiset.ofList (List.ofFn z.1)).filter (fun p => p.1 ≠ p.2) =
        (Multiset.ofList (List.ofFn w.1)).filter (fun p => p.1 ≠ p.2) ∧
      Multiset.ofList (List.ofFn z.2) =
        Multiset.ofList (List.ofFn w.2) := by
  constructor
  · intro h
    constructor
    · exact (finitePart_orderedQ m n z).symm.trans
        ((congrArg (fun D : Diagram α => finitePart D.points) h).trans
          (finitePart_orderedQ m' n' w))
    · exact (essentialPart_orderedQ m n z).symm.trans
        ((congrArg (fun D : Diagram α => essentialPart D.points) h).trans
          (essentialPart_orderedQ m' n' w))
  · rintro ⟨hf, he⟩
    apply Diagram.ext
    change _ + _ = _ + _
    rw [hf, he]

private theorem finitePart_enumerate {α : Type u} [LinearOrder α] (D : Diagram α) :
    ∃ (m : ℕ) (x : Fin m → α × α),
      (Multiset.ofList (List.ofFn x)).filter (fun p => p.1 ≠ p.2) = finitePart D.points := by
  let l := (finitePart D.points).toList
  refine ⟨l.length, l.get, ?_⟩
  rw [List.ofFn_get, Multiset.coe_toList, finitePart_filter]

private theorem essentialPart_enumerate {α : Type u} [LinearOrder α] (D : Diagram α) :
    ∃ (n : ℕ) (y : Fin n → α),
      Multiset.ofList (List.ofFn y) = essentialPart D.points := by
  let l := (essentialPart D.points).toList
  refine ⟨l.length, l.get, ?_⟩
  rw [List.ofFn_get, Multiset.coe_toList]

theorem orderedQ_surjective {α : Type u} [LinearOrder α] (D : Diagram α) :
    ∃ (m n : ℕ) (z : (Fin m → α × α) × (Fin n → α)),
      orderedQ m n z = D := by
  obtain ⟨m, x, hx⟩ := finitePart_enumerate D
  obtain ⟨n, y, hy⟩ := essentialPart_enumerate D
  refine ⟨m, n, (x, y), ?_⟩
  apply Diagram.ext
  change _ + _ = D.points
  rw [hx, hy]
  exact split_reconstruct D.points

private theorem ofFn_removeNth {β : Type*} {m : ℕ}
    (x : Fin (m + 1) → β) (k : Fin (m + 1)) :
    Multiset.ofList (List.ofFn x) =
      Multiset.ofList (List.ofFn (Fin.removeNth k x)) + {x k} := by
  classical
  have henum {r : ℕ} (f : Fin r → β) :
      Multiset.ofList (List.ofFn f) = (Finset.univ : Finset (Fin r)).val.map f := by
    rw [List.ofFn_eq_map]
    change Multiset.map f (↑(List.finRange r) : Multiset (Fin r)) = _
    rw [← Finset.val_univ_fin]
  rw [henum x, henum (Fin.removeNth k x), Fin.univ_succAbove m k]
  simp only [Finset.cons_val, Multiset.map_cons, Finset.map_val, Multiset.map_map]
  change x k ::ₘ (Finset.univ : Finset (Fin m)).val.map (x ∘ k.succAbove) =
    (Finset.univ : Finset (Fin m)).val.map (fun i => x (k.succAbove i)) + {x k}
  rw [← Multiset.singleton_add]
  exact add_comm _ _

theorem orderedQ_zeroLength {α : Type u} [LinearOrder α] (m n : ℕ)
    (x : Fin (m + 1) → α × α) (y : Fin n → α)
    (k : Fin (m + 1)) (hk : (x k).1 = (x k).2) :
    orderedQ m n (Fin.removeNth k x, y) =
      orderedQ (m + 1) n (x, y) := by
  apply (orderedQ_eq_iff m n (m + 1) n (Fin.removeNth k x, y) (x, y)).mpr
  constructor
  · rw [ofFn_removeNth x k, Multiset.filter_add]
    simp [hk]
  · rfl

end TDA.Persistence
