import TDA.Persistence.Diagram
import TDA.Persistence.FiniteBarcode

universe u
namespace TDA.Persistence

variable {α : Type u} [LinearOrder α] {N : ℕ}

private def indexPoint (v : Fin N → α) (I : FiniteInterval N) : α × WithTop α :=
  (v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩,
   if hd : I.death < N then
     (v ⟨I.death, hd⟩ : WithTop α)
   else
     (⊤ : WithTop α))

private theorem indexPoint_positive (v : Fin N → α) (hv : StrictMono v)
    (I : FiniteInterval N) :
    ((indexPoint v I).1 : WithTop α) < (indexPoint v I).2 := by
  dsimp [indexPoint]
  split_ifs with hd
  · exact WithTop.coe_lt_coe.mpr (hv (show (⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩ : Fin N) < ⟨I.death, hd⟩ from I.birth_lt_death))
  · exact WithTop.coe_lt_top _

/-- Relabel finite index bars using the chosen constant-tail convention at death `N`. -/
def ofIndexBars (v : Fin N → α) (hv : StrictMono v)
    (B : Multiset (FiniteInterval N)) : Diagram α where
  points := B.map (indexPoint v)
  offDiagonal := by
    intro p hp
    rcases Multiset.mem_map.mp hp with ⟨I, _, rfl⟩
    exact ne_of_lt (indexPoint_positive v hv I)

theorem ofIndexBars_isPositive (v : Fin N → α) (hv : StrictMono v)
    (B : Multiset (FiniteInterval N)) :
    (ofIndexBars v hv B).IsPositive := by
  intro p hp
  rcases Multiset.mem_map.mp hp with ⟨I, _, rfl⟩
  exact indexPoint_positive v hv I

private theorem indexPoint_eq_finite (v : Fin N → α) (hv : StrictMono v)
    (I : FiniteInterval N) (b d : Fin N) :
    indexPoint v I = (v b, (v d : WithTop α)) ↔
      I.birth = b.val ∧ I.death = d.val := by
  constructor
  · intro h
    have hb : v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩ = v b :=
      congrArg Prod.fst h
    have hb' : I.birth = b.val := congrArg Fin.val (hv.injective hb)
    by_cases hd : I.death < N
    · have hdeath : (v ⟨I.death, hd⟩ : WithTop α) = (v d : WithTop α) := by
        simpa [indexPoint, hd] using congrArg Prod.snd h
      have hd' : I.death = d.val :=
        congrArg Fin.val (hv.injective (WithTop.coe_injective hdeath))
      exact ⟨hb', hd'⟩
    · have hdeath : (⊤ : WithTop α) = (v d : WithTop α) := by
        simpa [indexPoint, hd] using congrArg Prod.snd h
      simp at hdeath
  · rintro ⟨hb, hd⟩
    have hfin : I.death < N := hd ▸ d.isLt
    have hbi : (⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩ : Fin N) = b := Fin.ext hb
    have hdi : (⟨I.death, hfin⟩ : Fin N) = d := Fin.ext hd
    simp [indexPoint, hfin, hbi, hdi]

private theorem indexPoint_eq_essential (v : Fin N → α) (hv : StrictMono v)
    (I : FiniteInterval N) (b : Fin N) :
    indexPoint v I = (v b, (⊤ : WithTop α)) ↔
      I.birth = b.val ∧ I.death = N := by
  constructor
  · intro h
    have hb : v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩ = v b :=
      congrArg Prod.fst h
    have hb' : I.birth = b.val := congrArg Fin.val (hv.injective hb)
    by_cases hd : I.death < N
    · have hdeath : (v ⟨I.death, hd⟩ : WithTop α) = (⊤ : WithTop α) := by
        simpa [indexPoint, hd] using congrArg Prod.snd h
      simp at hdeath
    · exact ⟨hb', Nat.le_antisymm I.death_le_size (Nat.le_of_not_gt hd)⟩
  · rintro ⟨hb, hd⟩
    have hbi : (⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩ : Fin N) = b := Fin.ext hb
    have hnot : ¬ I.death < N := by omega
    simp [indexPoint, hnot, hbi]

theorem ofIndexBars_count_finite (v : Fin N → α) (hv : StrictMono v)
    (B : Multiset (FiniteInterval N)) (b d : Fin N) :
    (ofIndexBars v hv B).points.count (v b, (v d : WithTop α)) =
      barcodeMultiplicity B b.val d.val := by
  classical
  rw [show (ofIndexBars v hv B).points = B.map (indexPoint v) from rfl,
    Multiset.count_map]
  rw [← Multiset.countP_eq_card_filter]
  refine Multiset.countP_congr rfl ?_
  intro I _
  apply propext
  simpa [eq_comm] using (indexPoint_eq_finite v hv I b d)

theorem ofIndexBars_count_essential (v : Fin N → α) (hv : StrictMono v)
    (B : Multiset (FiniteInterval N)) (b : Fin N) :
    (ofIndexBars v hv B).points.count (v b, (⊤ : WithTop α)) =
      barcodeMultiplicity B b.val N := by
  classical
  rw [show (ofIndexBars v hv B).points = B.map (indexPoint v) from rfl,
    Multiset.count_map]
  rw [← Multiset.countP_eq_card_filter]
  refine Multiset.countP_congr rfl ?_
  intro I _
  apply propext
  simpa [eq_comm] using (indexPoint_eq_essential v hv I b)

private theorem indexPoint_injective (v : Fin N → α) (hv : StrictMono v) :
    Function.Injective (indexPoint v) := by
  intro I J h
  have hb : I.birth = J.birth := by
    have hh := congrArg Prod.fst h
    exact congrArg Fin.val (hv.injective hh)
  have hd : I.death = J.death := by
    by_cases hi : I.death < N
    · by_cases hj : J.death < N
      · have hh : (v ⟨I.death, hi⟩ : WithTop α) = (v ⟨J.death, hj⟩ : WithTop α) := by
          simpa [indexPoint, hi, hj] using congrArg Prod.snd h
        exact congrArg Fin.val (hv.injective (WithTop.coe_injective hh))
      · have hh : (v ⟨I.death, hi⟩ : WithTop α) = (⊤ : WithTop α) := by
          simpa [indexPoint, hi, hj] using congrArg Prod.snd h
        simp at hh
    · by_cases hj : J.death < N
      · have hh : (⊤ : WithTop α) = (v ⟨J.death, hj⟩ : WithTop α) := by
          simpa [indexPoint, hi, hj] using congrArg Prod.snd h
        simp at hh
      · have hI := I.death_le_size
        have hJ := J.death_le_size
        omega
  cases I; cases J
  congr

theorem ofIndexBars_injective (v : Fin N → α) (hv : StrictMono v) :
    Function.Injective (ofIndexBars v hv) := by
  intro B C h
  apply Multiset.map_injective (indexPoint_injective v hv)
  exact congrArg Diagram.points h

private theorem indexPoint_slice (v : Fin N → α) (hv : StrictMono v)
    (I : FiniteInterval N) (i j : Fin N) :
    (indexPoint v I).1 ≤ v i ∧ (v j : WithTop α) < (indexPoint v I).2 ↔
      I.birth ≤ i.val ∧ j.val < I.death := by
  have hbirth : (indexPoint v I).1 ≤ v i ↔ I.birth ≤ i.val := by
    change v ⟨I.birth, lt_of_lt_of_le I.birth_lt_death I.death_le_size⟩ ≤ v i ↔ _
    exact (hv.le_iff_le).trans Fin.le_iff_val_le_val
  by_cases hd : I.death < N
  · have hdeath : (v j : WithTop α) < (indexPoint v I).2 ↔ j.val < I.death := by
      change (v j : WithTop α) < (if h : I.death < N then (v ⟨I.death, h⟩ : WithTop α) else ⊤) ↔ _
      simp only [dif_pos hd, WithTop.coe_lt_coe]
      exact (hv.lt_iff_lt).trans Fin.lt_def
    exact and_congr hbirth hdeath
  · have hterminal : I.death = N := by
      have hle := I.death_le_size
      omega
    have hdeath : (v j : WithTop α) < (indexPoint v I).2 ↔ j.val < I.death := by
      simp [indexPoint, hterminal, j.isLt]
    exact and_congr hbirth hdeath

theorem ofIndexBars_countP_grades (v : Fin N → α) (hv : StrictMono v)
    (B : Multiset (FiniteInterval N)) (i j : Fin N) :
    (ofIndexBars v hv B).points.countP
        (fun p => p.1 ≤ v i ∧ (v j : WithTop α) < p.2) =
      B.countP (fun I => I.birth ≤ i.val ∧ j.val < I.death) := by
  classical
  change (B.map (indexPoint v)).countP
    (fun p => p.1 ≤ v i ∧ (v j : WithTop α) < p.2) = _
  rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter]
  refine Multiset.countP_congr rfl ?_
  intro I _
  exact propext (indexPoint_slice v hv I i j)

end TDA.Persistence
