import TDA.Persistence.Reduction.PivotBarcode
namespace TDA.Persistence.Reduction
variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

theorem fixture_pairs_nodup (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) :
    (pivotIndexPairs degree R p).Nodup := by
  classical
  unfold pivotIndexPairs
  apply Multiset.Nodup.map _ (Finset.univ.nodup)
  intro x y h
  exact Subtype.ext (congrArg Prod.fst h)

theorem fixture_pairs_mem (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (hpiv : DistinctPivots R)
    (p : ℕ) (i j : Fin m) :
    (i,j) ∈ pivotIndexPairs degree R p ↔
      degree i = p ∧ columnPivot (R.col j) = some i := by
  classical
  unfold pivotIndexPairs
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, h⟩
    have hi : x.val = i := congrArg Prod.fst h
    have hj : deathOfPivot R x.val x.property.1 = j := congrArg Prod.snd h
    exact ⟨hi ▸ x.property.2, by rw [← hi, ← hj]; exact deathOfPivot_spec R _ _⟩
  · rintro ⟨hd,hj⟩
    let x : {i : Fin m // IsPivot R i ∧ degree i = p} := ⟨i, ⟨j,hj⟩,hd⟩
    exact ⟨x, Prod.ext rfl (deathOfPivot_unique R hpiv i j x.property.1 hj)⟩

theorem fixture_essential_nodup (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) :
    (pivotEssentialIndices degree R p).Nodup := by
  classical
  unfold pivotEssentialIndices
  exact Multiset.Nodup.map Subtype.val_injective (Finset.univ.nodup)

theorem fixture_essential_mem (degree : Fin m → ℕ)
    (R : Matrix (Fin m) (Fin m) k) (p : ℕ) (i : Fin m) :
    i ∈ pivotEssentialIndices degree R p ↔ IsEssential R i ∧ degree i = p := by
  classical
  simp [pivotEssentialIndices]
end TDA.Persistence.Reduction
