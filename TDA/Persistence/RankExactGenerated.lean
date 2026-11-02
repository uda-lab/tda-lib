import TDA.Persistence.RankExactKernel

/-!
# Rank exactness from generation at a bottom element

Surjective structure maps on the left term force rank exactness of a pointwise short exact
sequence. A bottom-generated term has these surjections, and bottom generation descends along
componentwise-surjective maps, including the actual categorical cokernel projection. The
resulting kernel-row theorem uses the actual categorical kernels of the supplied maps.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence

open CategoryTheory CategoryTheory.Limits

variable {k : Type u} [Field k] {P : Type} [PartialOrder P]
  {A B C D : PModule.{u,0,u} k P}

/-- Every element of a module is generated from the fiber at the least index. -/
def GeneratedAtBottom [OrderBot P] (M : PModule.{u,0,u} k P) : Prop :=
  ∀ p, Function.Surjective (structureMapLinear M (show (⊥ : P) ≤ p from bot_le))

namespace GeneratedAtBottom

/-- Generation at bottom makes every structure map surjective. -/
theorem structureMap_surjective [OrderBot P] {M : PModule.{u,0,u} k P}
    (hM : GeneratedAtBottom M) {a b : P} (hab : a ≤ b) :
    Function.Surjective (structureMapLinear M hab) := by
  intro y
  obtain ⟨x, hx⟩ := hM b y
  refine ⟨structureMapLinear M (show (⊥ : P) ≤ a from bot_le) x, ?_⟩
  have hbotA : (⊥ : P) ≤ a := bot_le
  have hbotB : (⊥ : P) ≤ b := bot_le
  have htrans : hbotA.trans hab = hbotB := Subsingleton.elim _ _
  calc
    structureMapLinear M hab (structureMapLinear M hbotA x) =
        structureMapLinear M (hbotA.trans hab) x := by
          rw [← LinearMap.comp_apply, ← structureMapLinear_comp]
    _ = structureMapLinear M hbotB x := by rw [htrans]
    _ = y := hx

/-- Bottom generation passes through a componentwise-surjective natural transformation. -/
theorem of_surjective [OrderBot P] {M N : PModule.{u,0,u} k P}
    (hM : GeneratedAtBottom M) (q : M ⟶ N)
    (hq : ∀ p, Function.Surjective (q.app p).hom) : GeneratedAtBottom N := by
  change ∀ p, Function.Surjective
    (structureMapLinear N (show (⊥ : P) ≤ p from bot_le))
  intro p y
  obtain ⟨x, hx⟩ := hq p y
  obtain ⟨x₀, hx₀⟩ := hM p x
  refine ⟨(q.app ⊥).hom x₀, ?_⟩
  have hn := congrArg (fun f : M.obj ⊥ ⟶ N.obj p => f.hom x₀)
    (q.naturality (homOfLE (show (⊥ : P) ≤ p from bot_le)))
  change (q.app p).hom
      (structureMapLinear M (show (⊥ : P) ≤ p from bot_le) x₀) =
    structureMapLinear N (show (⊥ : P) ≤ p from bot_le) ((q.app ⊥).hom x₀) at hn
  rw [hx₀, hx] at hn
  exact hn.symm

/-- The actual categorical cokernel projection is componentwise surjective. -/
theorem cokernel_projection_surjective {M N : PModule.{u,0,u} k P}
    (f : M ⟶ N) (p : P) :
    Function.Surjective ((cokernel.π f).app p).hom := by
  haveI : Epi (cokernel.π f) := inferInstance
  have hpi : Epi ((cokernel.π f).app p) :=
    (NatTrans.epi_iff_epi_app (cokernel.π f)).mp (inferInstance : Epi (cokernel.π f)) p
  exact (ModuleCat.epi_iff_surjective _).mp hpi

/-- The actual categorical cokernel of a bottom-generated module remains bottom-generated. -/
theorem cokernel [OrderBot P] {M N : PModule.{u,0,u} k P}
    (f : M ⟶ N) (hN : GeneratedAtBottom N) : GeneratedAtBottom (cokernel f) :=
  of_surjective hN (cokernel.π f) (cokernel_projection_surjective f)

end GeneratedAtBottom

namespace IsPointwiseShortExact

/-- If the left maps of a pointwise short exact row are surjective, the row is rank exact.
The middle term is assumed pointwise finite dimensional, as required by `IsRankExact`. -/
theorem rankExact_of_surjective_left {ι : A ⟶ B} {π : B ⟶ C}
    (hs : IsPointwiseShortExact ι π)
    (hι : ∀ {a b : P} (hab : a ≤ b),
      Function.Surjective (structureMapLinear A hab))
    (hB : ∀ p, FiniteDimensional k (B.obj p)) : IsRankExact ι π where
  toIsPointwiseShortExact := hs
  finiteDimensional := hB
  rank_add := by
    intro a b hab
    letI := hB a
    apply (hs.rank_add_iff_lift_kernel hab).mpr
    intro cₐ hcₐ
    obtain ⟨bₐ, hbₐ⟩ := hs.surjective a cₐ
    have hdie : (π.app b).hom (structureMapLinear B hab bₐ) = 0 := by
      have hn := congrArg (fun f : B.obj a ⟶ C.obj b => f.hom bₐ)
        (π.naturality (homOfLE hab))
      change (π.app b).hom (structureMapLinear B hab bₐ) =
        structureMapLinear C hab ((π.app a).hom bₐ) at hn
      simpa [hbₐ, hcₐ] using hn
    have himage : structureMapLinear B hab bₐ ∈ LinearMap.range (ι.app b).hom := by
      rw [hs.range_eq_ker b]
      exact hdie
    obtain ⟨a_b, ha_b⟩ := himage
    obtain ⟨aₐ, haₐ⟩ := hι hab a_b
    let b₀ := bₐ - (ι.app a).hom aₐ
    refine ⟨b₀, ?_, ?_⟩
    · have hzero : (π.app a).hom ((ι.app a).hom aₐ) = 0 := by
        have hc := congrArg (fun f : A ⟶ C => (f.app a).hom aₐ) hs.comp_eq_zero
        exact hc
      simp [b₀, map_sub, hbₐ, hzero]
    · have hn := congrArg (fun f : A.obj a ⟶ B.obj b => f.hom aₐ)
        (ι.naturality (homOfLE hab))
      change (ι.app b).hom (structureMapLinear A hab aₐ) =
        structureMapLinear B hab ((ι.app a).hom aₐ) at hn
      calc
        structureMapLinear B hab b₀ =
            structureMapLinear B hab bₐ -
              structureMapLinear B hab ((ι.app a).hom aₐ) := by simp [b₀]
        _ = (ι.app b).hom a_b -
              (ι.app b).hom (structureMapLinear A hab aₐ) := by
                rw [← ha_b, hn.symm]
        _ = 0 := by rw [haₐ]; simp

/-- The bottom-generated specialization of the short-exact rank criterion. -/
theorem rankExact_of_generatedAtBottom [OrderBot P] {ι : A ⟶ B} {π : B ⟶ C}
    (hs : IsPointwiseShortExact ι π) (hA : GeneratedAtBottom A)
    (hB : ∀ p, FiniteDimensional k (B.obj p)) : IsRankExact ι π :=
  rankExact_of_surjective_left hs hA.structureMap_surjective hB

end IsPointwiseShortExact

/-- The actual categorical lift `B → kernel c` induced by an exact pair `B → C → D`. -/
noncomputable def kernelRowLift {b : B ⟶ C} {c : C ⟶ D}
    (hC : ∀ p, LinearMap.range (b.app p).hom = LinearMap.ker (c.app p).hom) :
    B ⟶ kernel c := kernel.lift c b
      (IsPointwiseShortExact.comp_eq_zero_of_range_eq_ker b c hC)

@[simp] theorem kernelRowLift_ι {b : B ⟶ C} {c : C ⟶ D}
    (hC : ∀ p, LinearMap.range (b.app p).hom = LinearMap.ker (c.app p).hom) :
    kernelRowLift hC ≫ kernel.ι c = b :=
  kernel.lift_ι c b (IsPointwiseShortExact.comp_eq_zero_of_range_eq_ker b c hC)

private noncomputable def kernelRowLeftLift {a : A ⟶ B} {b : B ⟶ C}
    (hB : ∀ p, LinearMap.range (a.app p).hom = LinearMap.ker (b.app p).hom) :
    A ⟶ kernel b := kernel.lift b a
      (IsPointwiseShortExact.comp_eq_zero_of_range_eq_ker a b hB)

private theorem kernelRowLeftLift_surjective {a : A ⟶ B} {b : B ⟶ C}
    (hB : ∀ p, LinearMap.range (a.app p).hom = LinearMap.ker (b.app p).hom) (p : P) :
    Function.Surjective ((kernelRowLeftLift hB).app p).hom := by
  intro z
  have hz : ((kernel.ι b).app p).hom z ∈ LinearMap.ker (b.app p).hom := by
    have h := congrArg (fun f : kernel b ⟶ C => (f.app p).hom z) (kernel.condition b)
    exact h
  rw [← hB p] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, ?_⟩
  apply RankKernel.injective b p
  have he := congrArg (fun f : A ⟶ B => (f.app p).hom x)
    (kernel.lift_ι b a
      (IsPointwiseShortExact.comp_eq_zero_of_range_eq_ker a b hB))
  exact he.trans hx

private theorem kernelRowLift_surjective {b : B ⟶ C} {c : C ⟶ D}
    (hC : ∀ p, LinearMap.range (b.app p).hom = LinearMap.ker (c.app p).hom) (p : P) :
    Function.Surjective ((kernelRowLift hC).app p).hom := by
  intro z
  have hz : ((kernel.ι c).app p).hom z ∈ LinearMap.ker (c.app p).hom := by
    have h := congrArg (fun f : kernel c ⟶ D => (f.app p).hom z) (kernel.condition c)
    exact h
  rw [← hC p] at hz
  obtain ⟨x, hx⟩ := hz
  refine ⟨x, ?_⟩
  apply RankKernel.injective c p
  have he := congrArg (fun f : B ⟶ C => (f.app p).hom x) (kernelRowLift_ι hC)
  exact he.trans hx

private theorem kernelRowPointwiseShortExact {b : B ⟶ C} {c : C ⟶ D}
    (hC : ∀ p, LinearMap.range (b.app p).hom = LinearMap.ker (c.app p).hom) :
    IsPointwiseShortExact (kernel.ι b) (kernelRowLift hC) where
  injective := RankKernel.injective b
  surjective := kernelRowLift_surjective hC
  range_eq_ker := by
    intro p
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      apply RankKernel.injective c p
      have he := congrArg (fun f : B ⟶ C => (f.app p).hom
        (((kernel.ι b).app p).hom z)) (kernelRowLift_ι hC)
      change ((kernel.ι c).app p).hom
          (((kernelRowLift hC).app p).hom (((kernel.ι b).app p).hom z)) = _ at he
      rw [he]
      have hz := congrArg (fun f : kernel b ⟶ C => (f.app p).hom z) (kernel.condition b)
      change (b.app p).hom (((kernel.ι b).app p).hom z) = 0 at hz
      simpa using hz
    · intro hx
      have hbzero : (b.app p).hom x = 0 := by
        have he := congrArg (fun f : B ⟶ C => (f.app p).hom x)
          (kernelRowLift_ι hC)
        change ((kernel.ι c).app p).hom (((kernelRowLift hC).app p).hom x) =
          (b.app p).hom x at he
        rw [hx, map_zero] at he
        exact he.symm
      have hrange : x ∈ LinearMap.range ((kernel.ι b).app p).hom := by
        rw [RankKernel.range_eq_ker b p]
        exact hbzero
      obtain ⟨z, hz⟩ := hrange
      exact ⟨z, hz⟩

/-- For a pointwise-exact composable four-term sequence, the actual kernel row is rank exact.
The left kernel is bottom-generated by the actual lift from `A`, while surjectivity onto the
right kernel follows from exactness at `C`. -/
theorem rankExact_kernelRow [OrderBot P]
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
    (hB : ∀ p, LinearMap.range (a.app p).hom = LinearMap.ker (b.app p).hom)
    (hC : ∀ p, LinearMap.range (b.app p).hom = LinearMap.ker (c.app p).hom)
    (hA : GeneratedAtBottom A) (hBfd : ∀ p, FiniteDimensional k (B.obj p)) :
    IsRankExact (kernel.ι b) (kernelRowLift hC) := by
  have hAtoKer : GeneratedAtBottom (kernel b) := by
    apply GeneratedAtBottom.of_surjective hA (kernelRowLeftLift hB)
    exact kernelRowLeftLift_surjective hB
  exact IsPointwiseShortExact.rankExact_of_generatedAtBottom
    (kernelRowPointwiseShortExact hC) hAtoKer hBfd

end TDA.Persistence
