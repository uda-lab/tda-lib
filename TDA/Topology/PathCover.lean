import Mathlib.Topology.Subpath
import Mathlib.Topology.Sets.Opens
import Mathlib.Logic.Relation

/-!
# Path-local open-cover subdivision

A path `γ : Path x y` whose range is covered by a family of open sets `U i` admits a finite
monotone subdivision `0 = t₀ ≤ … ≤ tₙ = 1` of the unit interval together with a cover index
for each segment, such that `γ` maps the segment `[t_k, t_{k+1}]` into the selected member.
Adjacent segments share their endpoint, so consecutive chain points are joined inside single
members and every junction lies in the overlap of the two adjacent members.

The positive-mesh step is mathlib's `exists_monotone_Icc_subset_open_cover_unitInterval`, which
applies `lebesgue_number_lemma_of_metric` to the compact unit interval and takes a uniform
partition. Compactness enters only there. Repeated subdivision points are allowed: a degenerate
segment `[t, t]` maps to the single point `γ t`, which lies in the selected member, so every
statement holds for it unchanged; its subpath is `Path.refl` (`Path.subpath_self`).

The chain is indexed by `Fin (n + 1)`, the convention of `Path.concat`. The cover index is an
arbitrary `Sort`. No local path connectedness, Hausdorffness, compactness or nonemptiness of the
space is assumed. The module depends on mathlib only and is independent of the Reeb modules;
see `docs/math/path-cover.md`.
-/

open Set unitInterval Fin

namespace TDA.Topology

variable {X : Type*} [TopologicalSpace X] {ι : Sort*} {x y : X}

/-- Finite subdivision: segment `k` of `[0, 1]` maps into the cover member `U (i k)`. -/
theorem exists_subdivision (γ : Path x y) {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : range γ ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I) (i : Fin n → ι), t 0 = 0 ∧ t (last n) = 1 ∧
      Monotone t ∧ ∀ k : Fin n, γ '' Icc (t k.castSucc) (t k.succ) ⊆ U (i k) := by
  obtain ⟨t, t0, tmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (c := fun i => γ ⁻¹' U i)
      (fun i => (hU i).preimage γ.continuous)
      (fun s _ => by simpa using hcov (mem_range_self s))
  choose i hi using hsub
  refine ⟨n, fun k => t k, fun k => i k, t0, hn n le_rfl, fun a b hab => tmono hab, fun k => ?_⟩
  rw [image_subset_iff]
  simpa using hi k

/-- Restricted-path form: each segment's subpath of `γ` stays inside its cover member. -/
theorem exists_subpath_chain (γ : Path x y) {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : range γ ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I) (i : Fin n → ι), t 0 = 0 ∧ t (last n) = 1 ∧
      Monotone t ∧ ∀ k : Fin n, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U (i k) := by
  obtain ⟨n, t, i, t0, tn, tmono, hsub⟩ := exists_subdivision γ hU hcov
  refine ⟨n, t, i, t0, tn, tmono, fun k => ?_⟩
  rw [Path.range_subpath_of_le _ _ _ (tmono (castSucc_le_succ k))]
  exact hsub k

/-- Overlap-chain form: `x` and `y` are linked by finitely many points, consecutive ones joined
inside one cover member; each junction lies in the overlap of the two adjacent members. -/
theorem exists_overlap_chain (γ : Path x y) {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : range γ ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (p : Fin (n + 1) → X) (i : Fin n → ι), p 0 = x ∧ p (last n) = y ∧
      (∀ k : Fin n, JoinedIn (U (i k)) (p k.castSucc) (p k.succ)) ∧
      ∀ (k : ℕ) (hk : k + 1 < n),
        p ⟨k + 1, by omega⟩ ∈ U (i ⟨k, by omega⟩) ∩ U (i ⟨k + 1, hk⟩) := by
  obtain ⟨n, t, i, t0, tn, tmono, hsub⟩ := exists_subpath_chain γ hU hcov
  have hJ : ∀ k : Fin n, JoinedIn (U (i k)) (γ (t k.castSucc)) (γ (t k.succ)) := fun k =>
    ⟨γ.subpath _ _, fun s => hsub k (mem_range_self s)⟩
  refine ⟨n, γ ∘ t, i, by simp [t0], by simp [tn], hJ, fun k hk => ⟨?_, ?_⟩⟩
  · exact (hJ ⟨k, by omega⟩).target_mem
  · exact (hJ ⟨k + 1, hk⟩).source_mem

/-- Relational overlap-chain form, the shape a gluing proof eliminates: `x` and `y` are related
by the reflexive-transitive closure of "joined inside a single cover member". -/
theorem reflTransGen_of_path (γ : Path x y) {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : range γ ⊆ ⋃ i, U i) :
    Relation.ReflTransGen (fun a b => ∃ i, JoinedIn (U i) a b) x y := by
  obtain ⟨n, p, i, p0, pn, hJ, -⟩ := exists_overlap_chain γ hU hcov
  have key : ∀ (m : ℕ) (hm : m < n + 1),
      Relation.ReflTransGen (fun a b => ∃ i, JoinedIn (U i) a b) (p 0) (p ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro hm
      exact (ih (by omega)).tail ⟨i ⟨m, by omega⟩, hJ ⟨m, by omega⟩⟩
  have := key n (by omega)
  rwa [p0, show (⟨n, by omega⟩ : Fin (n + 1)) = last n from rfl, pn] at this

/-- `Joined` form: it suffices that the cover covers the path component of `x`. -/
theorem reflTransGen_of_joined (h : Joined x y) {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : pathComponent x ⊆ ⋃ i, U i) :
    Relation.ReflTransGen (fun a b => ∃ i, JoinedIn (U i) a b) x y := by
  obtain ⟨γ⟩ := h
  refine reflTransGen_of_path γ hU ?_
  rintro _ ⟨s, rfl⟩
  exact hcov ⟨(γ.subpath 0 s).cast (by simp) rfl⟩

/-- `TopologicalSpace.Opens` form: the image of `γ` lies in an open `W`, and the open family `V`
covers `W`. The openness of `W` is not used. -/
theorem exists_subdivision_opens (γ : Path x y) {W : TopologicalSpace.Opens X}
    (V : ι → TopologicalSpace.Opens X) (hγ : ∀ s, γ s ∈ W) (hWV : W ≤ ⨆ i, V i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I) (i : Fin n → ι), t 0 = 0 ∧ t (last n) = 1 ∧
      Monotone t ∧ ∀ k : Fin n, γ '' Icc (t k.castSucc) (t k.succ) ⊆ V (i k) :=
  exists_subdivision γ (fun i => (V i).isOpen) (by
    rintro _ ⟨s, rfl⟩
    simpa [TopologicalSpace.Opens.mem_iSup] using hWV (hγ s))

/-- Preimage-subspace form, the topological input of component gluing: a path inside the
preimage subspace `f ⁻¹ W` gives a chain of points, consecutive ones joined inside a single
preimage subspace `f ⁻¹ (V i)`. `V i ≤ W` is not assumed, and no component functor is used. -/
theorem reflTransGen_preimage {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    {W : TopologicalSpace.Opens Y} (V : ι → TopologicalSpace.Opens Y) (hWV : W ≤ ⨆ i, V i)
    {a b : {x : X // f x ∈ W}} (h : Joined a b) :
    Relation.ReflTransGen
      (fun a b : {x : X // f x ∈ W} => ∃ i, ∃ (ha : f a.1 ∈ V i) (hb : f b.1 ∈ V i),
        Joined (⟨a.1, ha⟩ : {x : X // f x ∈ V i}) ⟨b.1, hb⟩) a b := by
  have hopen : ∀ i, IsOpen {s : {x : X // f x ∈ W} | f s.1 ∈ V i} := fun i =>
    (V i).isOpen.preimage (f.continuous.comp continuous_subtype_val)
  refine Relation.ReflTransGen.mono ?_ a b (reflTransGen_of_joined h hopen (fun z _ => ?_))
  · rintro c d ⟨i, γ, hγ⟩
    refine ⟨i, by simpa using hγ 0, by simpa using hγ 1, ⟨?_⟩⟩
    exact
      { toFun := fun s => ⟨(γ s).1, hγ s⟩
        continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _
        source' := by ext; simp
        target' := by ext; simp }
  · simpa [TopologicalSpace.Opens.mem_iSup] using hWV z.2

end TDA.Topology
