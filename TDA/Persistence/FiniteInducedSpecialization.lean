import TDA.Persistence.FiniteInducedMatching

/-!
# Mono, epi and identity specializations of the image-induced matching

An isomorphic image factor preserves the canonical barcode and its original list
labels. The two ordinal embeddings are then inverse transports, so the constructed
matching agrees with the existing mono and epi correspondences.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteBarcode

open CategoryTheory

variable {s : ℕ}

private theorem occurrence_cast {B C : Multiset (FiniteInterval s)} (h : B = C)
    (i : BarcodeOccurrence s B) :
    occurrence C (cast (congrArg (BarcodeOccurrence s) h) i) = occurrence B i := by
  cases h
  rfl

private theorem deathOrdinal_cast {B C : Multiset (FiniteInterval s)} (h : B = C)
    (i : BarcodeOccurrence s B) :
    deathOrdinal C (cast (congrArg (BarcodeOccurrence s) h) i) = deathOrdinal B i := by
  cases h
  rfl

private theorem birthOrdinal_cast {B C : Multiset (FiniteInterval s)} (h : B = C)
    (i : BarcodeOccurrence s B) :
    birthOrdinal C (cast (congrArg (BarcodeOccurrence s) h) i) = birthOrdinal B i := by
  cases h
  rfl

variable {k : Type u} [Field k]
variable {M N : PModule.{u,0,u} k (Fin s)}
variable [∀ i, FiniteDimensional k (M.obj i)] [∀ i, FiniteDimensional k (N.obj i)]

private theorem mono_eq_cast (g : M ⟶ N) (hg : ∀ i, Function.Injective (g.app i).hom)
    (h : rankBarcode M = rankBarcode N) (i : BarcodeOccurrence s (rankBarcode M)) :
    monoEmbedding g hg i = cast (congrArg (BarcodeOccurrence s) h) i := by
  apply (monoEmbedding_eq_iff g hg i _).mpr
  exact ⟨congrArg FiniteInterval.death (occurrence_cast h i), deathOrdinal_cast h i⟩

private theorem epi_eq_cast (g : M ⟶ N) (hg : ∀ i, Function.Surjective (g.app i).hom)
    (h : rankBarcode N = rankBarcode M) (i : BarcodeOccurrence s (rankBarcode N)) :
    epiEmbedding g hg i = cast (congrArg (BarcodeOccurrence s) h) i := by
  apply (epiEmbedding_eq_iff g hg i _).mpr
  exact ⟨congrArg FiniteInterval.birth (occurrence_cast h i), birthOrdinal_cast h i⟩

private noncomputable def componentwiseIso (g : M ⟶ N)
    (hi : ∀ i, Function.Injective (g.app i).hom)
    (hs : ∀ i, Function.Surjective (g.app i).hom) : M ≅ N :=
  NatIso.ofComponents
    (fun i => (LinearEquiv.ofBijective (g.app i).hom ⟨hi i, hs i⟩).toModuleIso)
    (fun {_ _} h => g.naturality h)

private theorem mono_epi_cancel (g : M ⟶ N)
    (hi : ∀ i, Function.Injective (g.app i).hom)
    (hs : ∀ i, Function.Surjective (g.app i).hom) (a : BarcodeOccurrence s (rankBarcode N)) :
    monoEmbedding g hi (epiEmbedding g hs a) = a := by
  have h := rankBarcode_eq_of_iso (componentwiseIso g hi hs)
  rw [mono_eq_cast g hi h, epi_eq_cast g hs h.symm]
  simp

private theorem epi_mono_cancel (g : M ⟶ N)
    (hi : ∀ i, Function.Injective (g.app i).hom)
    (hs : ∀ i, Function.Surjective (g.app i).hom) (a : BarcodeOccurrence s (rankBarcode M)) :
    epiEmbedding g hs (monoEmbedding g hi a) = a := by
  have h := rankBarcode_eq_of_iso (componentwiseIso g hi hs)
  rw [epi_eq_cast g hs h.symm, mono_eq_cast g hi h]
  simp

/-- For a componentwise injection the constructed partial matching is the existing
canonical mono embedding on every source occurrence. -/
theorem inducedMap_of_injective (f : M ⟶ N)
    (hf : ∀ i, Function.Injective (f.app i).hom) (i : BarcodeOccurrence s (rankBarcode M)) :
    inducedMap f i = some (monoEmbedding f hf i) := by
  let a := monoEmbedding (toFiniteImage f) (toFiniteImage_injective f hf) i
  have ha : imageSourceEmbedding f a = i :=
    epi_mono_cancel (toFiniteImage f) (toFiniteImage_injective f hf)
      (toFiniteImage_surjective f) i
  have hcomp := monoEmbedding_comp (toFiniteImage f) (fromFiniteImage f)
    (toFiniteImage_injective f hf) (fromFiniteImage_injective f)
  change monoEmbedding f hf =
    (monoEmbedding (toFiniteImage f) (toFiniteImage_injective f hf)).trans
      (monoEmbedding (fromFiniteImage f) (fromFiniteImage_injective f)) at hcomp
  have hj : imageTargetEmbedding f a = monoEmbedding f hf i :=
    (congrArg (fun e : BarcodeOccurrence s (rankBarcode M) ↪
      BarcodeOccurrence s (rankBarcode N) => e i) hcomp).symm
  exact (inducedMap_eq_some_iff f _ _).mpr ⟨a, ha, hj⟩

/-- For a componentwise surjection the constructed matching is the reverse graph
of the existing canonical epi embedding. -/
theorem inducedMap_of_surjective_iff (f : M ⟶ N)
    (hf : ∀ i, Function.Surjective (f.app i).hom)
    (i : BarcodeOccurrence s (rankBarcode M)) (j : BarcodeOccurrence s (rankBarcode N)) :
    inducedMap f i = some j ↔ epiEmbedding f hf j = i := by
  let hs := fromFiniteImage_surjective f hf
  have hcomp := epiEmbedding_comp (toFiniteImage f) (fromFiniteImage f)
    (toFiniteImage_surjective f) hs
  change epiEmbedding f hf =
    (epiEmbedding (fromFiniteImage f) hs).trans
      (epiEmbedding (toFiniteImage f) (toFiniteImage_surjective f)) at hcomp
  have hc (a : BarcodeOccurrence s (rankBarcode N)) :
      epiEmbedding f hf a = imageSourceEmbedding f
        (epiEmbedding (fromFiniteImage f) hs a) :=
    congrArg (fun e : BarcodeOccurrence s (rankBarcode N) ↪
      BarcodeOccurrence s (rankBarcode M) => e a) hcomp
  constructor
  · intro h
    obtain ⟨a, ha, hj⟩ := (inducedMap_eq_some_iff f i j).mp h
    rw [hc, ← hj]
    change imageSourceEmbedding f (epiEmbedding (fromFiniteImage f) hs
      (monoEmbedding (fromFiniteImage f) (fromFiniteImage_injective f) a)) = i
    rw [epi_mono_cancel, ha]
  · intro h
    refine (inducedMap_eq_some_iff f i j).mpr
      ⟨epiEmbedding (fromFiniteImage f) hs j, (hc j).symm.trans h, ?_⟩
    exact mono_epi_cancel (fromFiniteImage f) (fromFiniteImage_injective f) hs j

/-- The actual image-induced matching of an identity matches each occurrence to itself. -/
theorem inducedMap_id (M : PModule.{u,0,u} k (Fin s))
    [∀ i, FiniteDimensional k (M.obj i)] (i : BarcodeOccurrence s (rankBarcode M)) :
    inducedMap (𝟙 M) i = some i := by
  rw [inducedMap_of_injective (𝟙 M) (fun _ => Function.injective_id), monoEmbedding_id]
  rfl

end TDA.Persistence.FiniteBarcode
