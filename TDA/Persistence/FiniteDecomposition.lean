import TDA.Persistence.IntervalExtraction
import TDA.Persistence.RankBarcodeIso

/-!
# Finite interval decomposition and complete-rank classification

An earliest-birth interval splits off a nonzero finite persistence module. Induction on the
sum of the fiber dimensions constructs a natural isomorphism to a finite barcode realization.
Only after constructing that isomorphism do rank invariance and the barcode round trip identify
the multiset with `rankBarcode`. The multiset is canonical; the chosen isomorphism is not.
-/

universe u

namespace TDA.Persistence

open CategoryTheory

variable {N : ℕ} {k : Type u} [Field k]

/-- Every pointwise finite-dimensional module on a finite chain is naturally isomorphic to
a finite list of interval modules. The proof inducts on total fiber dimension. -/
theorem exists_list_interval_decomposition (M : PModule.{u,0,u} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (M.obj i)] :
    ∃ xs : List (FiniteInterval N), Nonempty (M ≅ barcodeModuleOfList (k := k) xs) := by
  classical
  generalize hd : totalDimension M = d
  induction d using Nat.strong_induction_on generalizing M with
  | h d ih =>
    by_cases hzero : d = 0
    · exact ⟨[], ⟨zeroDimensionIso M (hd.trans hzero)⟩⟩
    · have hpos : 0 < totalDimension M := by omega
      obtain ⟨I, C, hC, ⟨e⟩, hlt⟩ := exists_interval_summand M hpos
      let : ∀ i : Fin N, FiniteDimensional k (C.obj i) := hC
      obtain ⟨xs, ⟨f⟩⟩ := ih (totalDimension C) (by omega) C rfl
      exact ⟨I :: xs, ⟨e ≪≫ pointwiseProdIso (Iso.refl _) f ≪≫
        barcodeModuleOfListConsIso I xs⟩⟩

/-- A finite interval decomposition exists without any supplied basis or decomposition. -/
theorem exists_barcode_decomposition (M : PModule.{u,0,u} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (M.obj i)] :
    ∃ B : Multiset (FiniteInterval N), Nonempty (M ≅ barcodeModule (k := k) B) := by
  obtain ⟨xs, ⟨e⟩⟩ := exists_list_interval_decomposition M
  exact ⟨↑xs, ⟨e ≪≫ barcodeModuleOfListIso xs⟩⟩

/-- A genuine natural isomorphism to the realization of the canonical rank barcode exists. -/
theorem nonempty_rankBarcodeIso (M : PModule.{u,0,u} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (M.obj i)] :
    Nonempty (M ≅ barcodeModule (k := k) (rankBarcode M)) := by
  obtain ⟨B, ⟨e⟩⟩ := exists_barcode_decomposition M
  have hB : rankBarcode M = B := rankBarcode_eq_of_iso_barcodeModule B e
  exact ⟨e ≪≫ eqToIso (congrArg (barcodeModule (k := k)) hB.symm)⟩

/-- A chosen, generally noncanonical natural isomorphism to the canonical barcode realization.
The choice depends on interval generators and complementary subspaces. -/
noncomputable def rankBarcodeIso (M : PModule.{u,0,u} k (Fin N))
    [∀ i : Fin N, FiniteDimensional k (M.obj i)] :
    M ≅ barcodeModule (k := k) (rankBarcode M) :=
  Classical.choice (nonempty_rankBarcodeIso M)

variable (M L : PModule.{u,0,u} k (Fin N))
variable [∀ i : Fin N, FiniteDimensional k (M.obj i)]
variable [∀ i : Fin N, FiniteDimensional k (L.obj i)]

/-- Canonical barcode equality classifies finite persistence modules up to natural isomorphism.
The reverse implication uses the constructed interval decompositions. -/
theorem nonempty_iso_iff_rankBarcode_eq :
    Nonempty (M ≅ L) ↔ rankBarcode M = rankBarcode L := by
  constructor
  · rintro ⟨e⟩
    exact rankBarcode_eq_of_iso e
  · intro h
    exact ⟨rankBarcodeIso M ≪≫ eqToIso (congrArg (barcodeModule (k := k)) h) ≪≫
      (rankBarcodeIso L).symm⟩

/-- The ranks of all structure maps form a complete invariant. Diagonal ranks alone
or diagonal and adjacent ranks alone do not suffice. -/
theorem nonempty_iso_iff_structureMapRank_eq :
    Nonempty (M ≅ L) ↔ ∀ (i j : Fin N) (hij : i ≤ j),
      structureMapRank M i j hij = structureMapRank L i j hij :=
  (nonempty_iso_iff_rankBarcode_eq M L).trans (rankBarcode_eq_iff M L)

/-- Any two interval decompositions of the same module have the same occurrence multiset.
This is uniqueness of multiplicities, not of generators, summands, or isomorphisms. -/
theorem barcode_decomposition_unique (B C : Multiset (FiniteInterval N))
    (e : M ≅ barcodeModule (k := k) B) (f : M ≅ barcodeModule (k := k) C) : B = C :=
  (rankBarcode_eq_of_iso_barcodeModule B e).symm.trans
    (rankBarcode_eq_of_iso_barcodeModule C f)

end TDA.Persistence
