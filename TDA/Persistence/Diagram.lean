import Mathlib

universe u
namespace TDA.Persistence

structure Diagram (α : Type u) [LinearOrder α] where
  points : Multiset (α × WithTop α)
  offDiagonal : ∀ p ∈ points, (p.1 : WithTop α) ≠ p.2

@[ext] theorem Diagram.ext {α : Type u} [LinearOrder α] {D E : Diagram α}
    (h : D.points = E.points) : D = E := by
  cases D; cases E; cases h; rfl

def Diagram.IsPositive {α : Type u} [LinearOrder α] (D : Diagram α) : Prop :=
  ∀ p ∈ D.points, (p.1 : WithTop α) < p.2

def orderedQ {α : Type u} [LinearOrder α] (m n : ℕ)
    (z : (Fin m → α × α) × (Fin n → α)) : Diagram α where
  points :=
    ((Multiset.ofList (List.ofFn z.1)).filter (fun p => p.1 ≠ p.2)).map
        (fun p => (p.1, (p.2 : WithTop α))) +
      (Multiset.ofList (List.ofFn z.2)).map
        (fun b => (b, (⊤ : WithTop α)))
  offDiagonal := by
    intro p hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · rcases Multiset.mem_map.mp hp with ⟨q, hq, rfl⟩
      have hne : q.1 ≠ q.2 := (Multiset.mem_filter.mp hq).2
      simpa using hne
    · rcases Multiset.mem_map.mp hp with ⟨b, hb, rfl⟩
      simp


private theorem ofFn_perm {β : Type*} {k : ℕ} (f : Fin k → β) (σ : Equiv.Perm (Fin k)) :
    (Multiset.ofList (List.ofFn (f ∘ σ))) = Multiset.ofList (List.ofFn f) := by
  exact Quot.sound (Equiv.Perm.ofFn_comp_perm σ f)

theorem orderedQ_perm {α : Type u} [LinearOrder α] (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (x : Fin m → α × α) (y : Fin n → α) :
    orderedQ m n (x ∘ σ, y ∘ τ) = orderedQ m n (x, y) := by
  apply Diagram.ext
  simp only [orderedQ, ofFn_perm]

private theorem count_ofFn {β : Type*} [DecidableEq β] {k : ℕ} (f : Fin k → β) (b : β) :
    (Multiset.ofList (List.ofFn f)).count b =
      (Finset.univ.filter (fun i : Fin k => f i = b)).card := by
  rw [List.ofFn_eq_map]
  change (Multiset.map f (Multiset.ofList (List.finRange k))).count b = _
  rw [Multiset.count_map]
  rw [← Finset.val_univ_fin k]
  calc
    (Multiset.filter (fun a : Fin k => b = f a) (Finset.univ : Finset (Fin k)).val).card =
        (Finset.filter (fun a : Fin k => b = f a) Finset.univ).card := by
          exact (congrArg Multiset.card
            (Finset.filter_val (p := fun a : Fin k => b = f a) (Finset.univ : Finset (Fin k)))).symm
    _ = (Finset.univ.filter (fun i : Fin k => f i = b)).card := by
      congr 1
      ext i
      simp [eq_comm]

private theorem finiteEmbed_injective {α : Type u} [LinearOrder α] :
    Function.Injective (fun p : α × α => (p.1, (p.2 : WithTop α))) := by
  intro p q h
  cases p with
  | mk a b =>
    cases q with
    | mk c d =>
      have h₁ : a = c := congrArg Prod.fst h
      have h₂ : b = d := by simpa using congrArg Prod.snd h
      simp [h₁, h₂]

theorem orderedQ_count_finite {α : Type u} [LinearOrder α] (m n : ℕ)
    (z : (Fin m → α × α) × (Fin n → α)) (b d : α) :
    (orderedQ m n z).points.count (b, (d : WithTop α)) =
      if b = d then 0 else
        (Finset.univ.filter (fun i : Fin m => z.1 i = (b, d))).card := by
  classical
  simp only [orderedQ, Multiset.count_add]
  have he : ((Multiset.ofList (List.ofFn z.2)).map
      (fun a => (a, (⊤ : WithTop α)))).count (b, (d : WithTop α)) = 0 := by
    rw [Multiset.count_eq_zero]
    intro h
    rcases Multiset.mem_map.mp h with ⟨a, _, ha⟩
    have htop : (⊤ : WithTop α) = (d : WithTop α) := congrArg Prod.snd ha
    simp at htop
  rw [he, Nat.add_zero]
  have hm := Multiset.count_map_eq_count'
      (fun p : α × α => (p.1, (p.2 : WithTop α)))
      ((Multiset.ofList (List.ofFn z.1)).filter (fun p => p.1 ≠ p.2))
      finiteEmbed_injective (b, d)
  change _ = _ at hm
  rw [hm, Multiset.count_filter, count_ofFn]
  simp

theorem orderedQ_count_essential {α : Type u} [LinearOrder α] (m n : ℕ)
    (z : (Fin m → α × α) × (Fin n → α)) (b : α) :
    (orderedQ m n z).points.count (b, (⊤ : WithTop α)) =
      (Finset.univ.filter (fun j : Fin n => z.2 j = b)).card := by
  classical
  simp only [orderedQ, Multiset.count_add]
  have hf : (((Multiset.ofList (List.ofFn z.1)).filter (fun p => p.1 ≠ p.2)).map
      (fun p => (p.1, (p.2 : WithTop α)))).count (b, (⊤ : WithTop α)) = 0 := by
    rw [Multiset.count_eq_zero]
    intro h
    rcases Multiset.mem_map.mp h with ⟨p, _, hp⟩
    have htop : (p.2 : WithTop α) = ⊤ := congrArg Prod.snd hp
    simp at htop
  rw [hf, Nat.zero_add]
  have hi : Function.Injective (fun a : α => (a, (⊤ : WithTop α))) := by
    intro a c h
    exact congrArg Prod.fst h
  rw [Multiset.count_map_eq_count' (fun a : α => (a, (⊤ : WithTop α))) _ hi b]
  exact count_ofFn z.2 b

theorem orderedQ_isPositive_iff {α : Type u} [LinearOrder α] (m n : ℕ)
    (z : (Fin m → α × α) × (Fin n → α)) :
    (orderedQ m n z).IsPositive ↔ ∀ i, (z.1 i).1 ≤ (z.1 i).2 := by
  constructor
  · intro hp i
    by_contra hn
    have hgt : (z.1 i).2 < (z.1 i).1 := lt_of_not_ge hn
    have hmem : ((z.1 i).1, ((z.1 i).2 : WithTop α)) ∈ (orderedQ m n z).points := by
      apply Multiset.mem_add.mpr
      left
      apply Multiset.mem_map.mpr
      refine ⟨z.1 i, ?_, rfl⟩
      apply Multiset.mem_filter.mpr
      constructor
      · exact List.mem_ofFn.mpr ⟨i, rfl⟩
      · exact ne_of_gt hgt
    have hlt : (z.1 i).1 < (z.1 i).2 := by
      simpa using hp _ hmem
    exact (not_lt_of_ge (le_of_lt hgt)) hlt
  · intro hle p hp
    change p ∈ (orderedQ m n z).points at hp
    rcases Multiset.mem_add.mp hp with hp | hp
    · rcases Multiset.mem_map.mp hp with ⟨q, hq, rfl⟩
      have hqmem : q ∈ Multiset.ofList (List.ofFn z.1) := (Multiset.mem_filter.mp hq).1
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hqmem
      have hqle : q.1 ≤ q.2 := by simpa [hi] using hle i
      have hqne : q.1 ≠ q.2 := (Multiset.mem_filter.mp hq).2
      have hqlt : q.1 < q.2 := lt_of_le_of_ne hqle hqne
      simpa using hqlt
    · rcases Multiset.mem_map.mp hp with ⟨b, _, rfl⟩
      simp
