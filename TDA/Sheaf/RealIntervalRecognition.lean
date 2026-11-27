import TDA.Sheaf.AlternatingDecomposition
import TDA.Sheaf.RealIntervalSections

/-!
# Recognition of interval diagrams and sheaves

An interval diagram is determined by its vertex dimensions and the invertibility of its
arrows within the interval. On the real line, it suffices to check sections and restrictions
on the basis of order-connected opens containing at most one breakpoint.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TDA.Persistence

namespace TDA.Sheaf.AlternatingDiagram

private theorem eq_of_alive_iff {n : ℕ} {J K : FiniteInterval (n + 1)}
    (h : ∀ j : Fin (n + 1), J.alive j ↔ K.alive j) : J = K := by
  have j : J.birth < n + 1 := J.birth_lt_death.trans_le J.death_le_size
  have k : K.birth < n + 1 := K.birth_lt_death.trans_le K.death_le_size
  have hj := (h ⟨J.birth, j⟩).mp ⟨le_rfl, J.birth_lt_death⟩
  have hk := (h ⟨K.birth, k⟩).mpr ⟨le_rfl, K.birth_lt_death⟩
  have jd : J.death - 1 < n + 1 := by have := J.death_le_size; omega
  have kd : K.death - 1 < n + 1 := by have := K.death_le_size; omega
  have hjd := (h ⟨J.death - 1, jd⟩).mp (by
    have := J.birth_lt_death
    change J.birth ≤ J.death - 1 ∧ J.death - 1 < J.death
    omega)
  have hkd := (h ⟨K.death - 1, kd⟩).mpr (by
    have := K.birth_lt_death
    change K.birth ≤ K.death - 1 ∧ K.death - 1 < K.death
    omega)
  cases J
  cases K
  simp_all [FiniteInterval.alive]
  omega

/-- A finite-dimensional diagram with dimension one on `J`, zero off `J`, and invertible
arrows between vertices of `J` is isomorphic to the interval diagram of `J`. -/
theorem nonempty_iso_interval_of_finrank {k : Type*} [Field k] {n : ℕ} {o : Fin n → Bool}
    (M : Diagram k o) [∀ X, FiniteDimensional k (M.obj X)] (J : FiniteInterval (n + 1))
    (hon : ∀ j, J.alive j → Module.finrank k (M.obj (vtx o j)) = 1)
    (hoff : ∀ j, ¬ J.alive j → Module.finrank k (M.obj (vtx o j)) = 0)
    (hmap : ∀ {i j} (h : Arrow o i j), J.alive i → J.alive j → IsIso (M.map (gen h))) :
    Nonempty (M ≅ interval o J) := by
  classical
  obtain ⟨xs, ⟨e⟩⟩ := exists_decomposition o M
  let B : Multiset (FiniteInterval (n + 1)) := xs
  have hdim (j : Fin (n + 1)) :
      Module.finrank k (M.obj (vtx o j)) = B.countP (fun K => K.alive j) := by
    rw [finrank_obj_eq_of_iso e, finrank_intervalSum_obj, ← Multiset.coe_countP]
  have hsupp {K : FiniteInterval (n + 1)} (hK : K ∈ B) {j} (hj : K.alive j) : J.alive j := by
    by_contra hn
    have := Multiset.countP_pos_of_mem (p := fun K => K.alive j) hK hj
    rw [← hdim, hoff j hn] at this
    omega
  have hnext {i j} (h : Arrow o i j) (hi : J.alive i) (hj : J.alive j) :
      ∃ K ∈ B, K.alive i ∧ K.alive j := by
    have := hmap h hi hj
    let f := (intervalSum (k := k) o xs).map (gen h)
    have hiso : IsIso ((e.app (vtx o i)).hom ≫ f) := by
      rw [show (e.app (vtx o i)).hom ≫ f =
        M.map (gen h) ≫ (e.app (vtx o j)).hom from (e.hom.naturality (gen h)).symm]
      infer_instance
    have := IsIso.of_isIso_comp_left (e.app (vtx o i)).hom f
    have hr := finrank_range_intervalSum_map (k := k) xs h
    rw [← Multiset.coe_countP] at hr
    change Module.finrank k (LinearMap.range f.hom) =
      B.countP (fun K => K.alive i ∧ K.alive j) at hr
    rw [LinearMap.range_eq_top.mpr (ModuleCat.epi_iff_surjective f |>.mp inferInstance),
      finrank_top, ← finrank_obj_eq_of_iso e, hon j hj] at hr
    exact Multiset.countP_pos.1 (by omega)
  let b : Fin (n + 1) := ⟨J.birth, J.birth_lt_death.trans_le J.death_le_size⟩
  have hb : J.alive b := ⟨le_rfl, J.birth_lt_death⟩
  have hunique {i} (hi : J.alive i) {K L} (hK : K ∈ B) (hL : L ∈ B)
      (hKi : K.alive i) (hLi : L.alive i) : K = L := by
    have hcard := (hdim i).symm.trans (hon i hi)
    rw [Multiset.countP_eq_card_filter, Multiset.card_eq_one] at hcard
    obtain ⟨A, hA⟩ := hcard
    have hmK : K ∈ B.filter (fun K => K.alive i) := Multiset.mem_filter.mpr ⟨hK, hKi⟩
    have hmL : L ∈ B.filter (fun K => K.alive i) := Multiset.mem_filter.mpr ⟨hL, hLi⟩
    rw [hA, Multiset.mem_singleton] at hmK hmL
    exact hmK.trans hmL.symm
  have hpos : 0 < B.countP (fun K => K.alive b) := by rw [← hdim, hon b hb]; decide
  obtain ⟨K, hK, hKb⟩ := Multiset.countP_pos.1 hpos
  have hfull (j : Fin (n + 1)) (hj : J.alive j) : K.alive j := by
    induction j using Fin.induction with
    | zero =>
      have he : (0 : Fin (n + 1)) = b := Fin.ext (by have := hj.1; simpa [b, eq_comm] using this)
      rwa [he]
    | succ i ih =>
      by_cases he : i.succ = b
      · rwa [he]
      have hi : J.alive i.castSucc := by
        have h₁ : J.birth ≤ i.val + 1 := hj.1
        have h₂ : i.val + 1 < J.death := hj.2
        have h₃ : i.val + 1 ≠ J.birth := fun h => he (Fin.ext h)
        exact ⟨by simpa using (show J.birth ≤ i.val by omega),
          by simpa using (show i.val < J.death by omega)⟩
      have hK' := ih hi
      rcases arrow_or_arrow o (i := i.castSucc) (j := i.succ) (Or.inl rfl) with hh | hh
      · obtain ⟨L, hL, hLi, hLj⟩ := hnext hh hi hj
        exact hunique hi hL hK hLi hK' ▸ hLj
      · obtain ⟨L, hL, hLj, hLi⟩ := hnext hh hj hi
        exact hunique hi hL hK hLi hK' ▸ hLj
  have hKJ : K = J := eq_of_alive_iff fun j => ⟨hsupp hK, hfull j⟩
  subst K
  have only (L : FiniteInterval (n + 1)) (hL : L ∈ B) : L = J := by
    let i : Fin (n + 1) := ⟨L.birth, L.birth_lt_death.trans_le L.death_le_size⟩
    have hi : L.alive i := ⟨le_rfl, L.birth_lt_death⟩
    exact hunique (hsupp hL hi) hL hK hi (hsupp hL hi)
  have hB : B = {J} := by
    have hcard := (hdim b).symm.trans (hon b hb)
    rw [Multiset.countP_eq_card_filter, Multiset.card_eq_one] at hcard
    obtain ⟨L, hL⟩ := hcard
    have he : B.filter (fun K => K.alive b) = B :=
      Multiset.filter_eq_self.2 fun K hK => (only K hK).symm ▸ hb
    rw [he] at hL
    have hm : L ∈ B := hL.symm ▸ Multiset.mem_singleton_self _
    rw [hL, only L hm]
  have hxs : xs = [J] := by simpa using Multiset.coe_eq_coe.mp hB
  subst xs
  exact ⟨e ≪≫ (isoBiprodZero (isZero_zero _)).symm⟩

end TDA.Sheaf.AlternatingDiagram

namespace TDA.Sheaf.RealStratification

/-- A nonempty order-connected set that is a union of strata is an interval set. -/
theorem exists_intervalSet_of_strata {m : ℕ} {p : Fin m → ℝ} (hp : StrictMono p)
    {I : Set ℝ} (hI : I.OrdConnected) (hne : I.Nonempty)
    (hs : ∀ ⦃v x y⦄, x ∈ stratum p v → y ∈ stratum p v → x ∈ I → y ∈ I) :
    ∃ J : FiniteInterval (2 * m + 1), intervalSet p J = I := by
  classical
  let s := Finset.univ.filter fun v : Fin (2 * m + 1) => (I ∩ stratum p v).Nonempty
  have hmem (v : Fin (2 * m + 1)) : v ∈ s ↔ (I ∩ stratum p v).Nonempty := by simp [s]
  obtain ⟨x, hx⟩ := hne
  obtain ⟨v, hv⟩ := exists_mem_stratum hp x
  have hn : s.Nonempty := ⟨v, (hmem v).2 ⟨x, hx, hv⟩⟩
  let b := s.min' hn
  let d := s.max' hn
  have hb := s.min'_mem hn
  have hd := s.max'_mem hn
  have hbd := s.min'_le d hd
  let J : FiniteInterval (2 * m + 1) :=
    ⟨b.val, d.val + 1, Nat.lt_succ_of_le hbd, d.isLt⟩
  refine ⟨J, ?_⟩
  ext y
  obtain ⟨w, hw⟩ := exists_mem_stratum hp y
  rw [mem_intervalSet_iff_alive hw]
  constructor
  · intro hj
    obtain ⟨l, hl, hl'⟩ := (hmem b).1 hb
    obtain ⟨r, hr, hr'⟩ := (hmem d).1 hd
    rcases lt_or_eq_of_le (show b ≤ w from hj.1) with hbw | rfl
    · rcases lt_or_eq_of_le (show w ≤ d from Nat.le_of_lt_succ hj.2) with hwd | rfl
      · exact hI.out hl hr ⟨(lt_of_mem_stratum hl' hw hbw).le,
          (lt_of_mem_stratum hw hr' hwd).le⟩
      · exact hs hr' hw hr
    · exact hs hl' hw hl
  · intro hy
    have h := (hmem w).2 ⟨y, hy, hw⟩
    exact ⟨s.min'_le w h, Nat.lt_succ_of_le (s.le_max' w h)⟩

end TDA.Sheaf.RealStratification

namespace TDA.Sheaf.RealConstructible

open AlternatingDiagram RealStratification

/-- An open meets an interval set in a nonempty relatively closed subset. -/
def MeetsClosed (I : Set ℝ) (U : Opens realLine) : Prop :=
  closure I ∩ U ⊆ I ∧ ((U : Set ℝ) ∩ I).Nonempty

variable {k : Type} [Field k] {m : ℕ} {p : Fin m → ℝ}

/-- An interval sheaf is recognized by its sections on the one-breakpoint basis and by
invertible restriction whenever both opens meet the interval in nonempty relatively closed
subsets. -/
theorem nonempty_iso_extension_interval_of_sections (hp : StrictMono p)
    (F : realLine.Sheaf (ModuleCat k)) (J : FiniteInterval (2 * m + 1))
    (hon : ∀ U, IsBasicOpen (breakpoints p) U → MeetsClosed (intervalSet p J) U →
      Nonempty (F.presheaf.obj (op U) ≅ ModuleCat.of k k))
    (hoff : ∀ U, IsBasicOpen (breakpoints p) U → ¬ MeetsClosed (intervalSet p J) U →
      IsZero (F.presheaf.obj (op U)))
    (hmap : ∀ ⦃U V : Opens realLine⦄ (h : U ≤ V),
      IsBasicOpen (breakpoints p) U → IsBasicOpen (breakpoints p) V →
      MeetsClosed (intervalSet p J) U → MeetsClosed (intervalSet p J) V →
      IsIso (F.presheaf.map (homOfLE h).op)) :
    Nonempty (F ≅ (extension k hp).obj (interval (orient m) J)) := by
  classical
  let G := (extension k hp).obj (interval (orient m) J)
  have hG := isConstructible_extension k hp (M := interval (orient m) J)
    (fun _ => inferInstance)
  have dim (U : Opens realLine) (hU : IsBasicOpen (breakpoints p) U) :
      Module.finrank k (G.presheaf.obj (op U)) = Module.finrank k (F.presheaf.obj (op U)) := by
    by_cases h : MeetsClosed (intervalSet p J) U
    · obtain ⟨e⟩ := hon U hU h
      rw [finrank_sections_extension_interval_eq_one k hp J hU.2.1 h.1 h.2,
        e.toLinearEquiv.finrank_eq, Module.finrank_self]
    · have hs := ModuleCat.subsingleton_of_isZero (hoff U hU h)
      rw [finrank_sections_extension_interval_eq_zero k hp J hU.2.1 h,
        Module.finrank_zero_of_subsingleton]
  have hF : IsConstructible (breakpoints p) F := by
    refine isConstructible_iff.2 ⟨fun U V h hU hV he => ?_, fun U hU => ?_⟩
    · have := (isConstructible_iff.1 hG).1 h hU hV he
      have hd := (asIso (G.presheaf.map (homOfLE h).op)).toLinearEquiv.finrank_eq
      by_cases hu : MeetsClosed (intervalSet p J) U <;>
        by_cases hv : MeetsClosed (intervalSet p J) V
      · exact hmap h hU hV hu hv
      · rw [finrank_sections_extension_interval_eq_zero k hp J hV.2.1 hv,
          finrank_sections_extension_interval_eq_one k hp J hU.2.1 hu.1 hu.2] at hd
        omega
      · rw [finrank_sections_extension_interval_eq_one k hp J hV.2.1 hv.1 hv.2,
          finrank_sections_extension_interval_eq_zero k hp J hU.2.1 hu] at hd
        omega
      · exact (hoff V hV hv).isIso (hoff U hU hu) _
    · by_cases h : MeetsClosed (intervalSet p J) U
      · exact (hon U hU h).some.toLinearEquiv.symm.finiteDimensional
      · have := ModuleCat.subsingleton_of_isZero (hoff U hU h)
        infer_instance
  let (X : Paths (Vertex (orient m))) := finiteDimensional_sections k hp hF X
  have dstar (j : Fin (2 * m + 1)) :
      Module.finrank k (((sections k p).obj F).obj (vtx (orient m) j)) =
        if J.alive j then 1 else 0 := by
    rw [sections_obj_obj, ← dim _ (isBasicOpen_star hp j),
      (extensionStarIso k hp (interval (orient m) J) j).toLinearEquiv.finrank_eq,
      finrank_interval_obj]
  have hgood (j : Fin (2 * m + 1)) (hj : J.alive j) :
      MeetsClosed (intervalSet p J) (star p j) := by
    by_contra hn
    have hd := dstar j
    rw [sections_obj_obj, ite_eq_left hj, ← dim _ (isBasicOpen_star hp j),
      finrank_sections_extension_interval_eq_zero k hp J (isBasicOpen_star hp j).2.1 hn] at hd
    omega
  obtain ⟨e⟩ := nonempty_iso_interval_of_finrank ((sections k p).obj F) J
    (fun j hj => by simp [dstar, hj]) (fun j hj => by simp [dstar, hj])
    (fun {i j} a hi hj => by
      rw [sections_map_gen]
      exact hmap _ (isBasicOpen_star hp j) (isBasicOpen_star hp i) (hgood j hj) (hgood i hi))
  exact ⟨(sectionsExtensionIso k hp).app ⟨F, hF⟩ ≪≫ (extension k hp).mapIso e⟩

end TDA.Sheaf.RealConstructible
