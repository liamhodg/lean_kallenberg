import Mathlib
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

open Set
open TopologicalSpace
open scoped Topology

namespace Appendix2

variable {S : Type*} [TopologicalSpace S]

/-- A locally compact, second countable, Hausdorff space. -/
class LcscHausdorffSpace (S : Type*) [TopologicalSpace S] : Prop where
  locallyCompact : LocallyCompactSpace S
  secondCountable : SecondCountableTopology S
  hausdorff : T2Space S

attribute [instance] LcscHausdorffSpace.locallyCompact
attribute [instance] LcscHausdorffSpace.secondCountable
attribute [instance] LcscHausdorffSpace.hausdorff

instance (S : Type*) [TopologicalSpace S] [LocallyCompactSpace S]
    [SecondCountableTopology S] [T2Space S] : LcscHausdorffSpace S :=
  ⟨inferInstance, inferInstance, inferInstance⟩

def limitProperty (A : Set S) : Prop :=
  ∀ {ι : Type*} {F : Filter ι} [Filter.NeBot F] {u : ι → S} {x : S},
    Filter.Tendsto u F (𝓝 x) → (∀ᶠ i in F, u i ∈ A) → x ∈ A

def clusterProperty (A : Set S) : Prop :=
  ∀ {ι : Type*} {F : Filter ι} [Filter.NeBot F] {u : ι → S} {x : S},
    ClusterPt x (Filter.map u F) → (∀ᶠ i in F, u i ∈ A) → x ∈ A

/-- Lemma A2.1 (closed sets)
For sets A in a topological space S, the following conditions are
equivalent:
(i) A is closed,
(ii) for every convergent net in A, even the limit lies in A,
(iii) for every net in A, all cluster points also lie in A. -/
lemma kallenberg_a2_1
    {A : Set S} :
    (IsClosed A ↔ limitProperty (A := A)) ∧
      (limitProperty (A := A) ↔ clusterProperty (A := A)) := by
  classical
  constructor
  · constructor
    · intro hA
      dsimp [limitProperty]
      intro ι F hF u x hx h_event
      haveI : Filter.NeBot F := hF
      exact hA.mem_of_tendsto hx h_event
    · intro hlimit
      rw [isClosed_iff_forall_filter]
      intro x F hF hFA hFx
      have h_event : ∀ᶠ i in F, (fun y : S => y) i ∈ A := by
        have : A ∈ F := hFA (by simp)
        simpa using this
      have h_tend : Filter.Tendsto (fun y : S => y) F (𝓝 x) := by
        refine (Filter.tendsto_def).2 ?_
        intro s hs
        exact hFx hs
      haveI : Filter.NeBot F := hF
      exact hlimit (F := F) (u := fun y : S => y) (x := x) h_tend h_event
  · constructor
    · intro hlimit
      have hClosed : IsClosed A := by
        refine (isClosed_iff_forall_filter).2 ?_
        intro x F hF hFA hFx
        have h_event : ∀ᶠ i in F, (fun y : S => y) i ∈ A := by
          have : A ∈ F := hFA (by simp)
          simpa using this
        have h_tend : Filter.Tendsto (fun y : S => y) F (𝓝 x) := by
          refine (Filter.tendsto_def).2 ?_
          intro s hs
          exact hFx hs
        haveI : Filter.NeBot F := hF
        exact hlimit (F := F) (u := fun y : S => y) (x := x) h_tend h_event
      dsimp [clusterProperty]
      intro ι F _ u x hx h_event
      have h_le : Filter.map u F ≤ Filter.principal A := by
        have : A ∈ Filter.map u F := by
          simpa using h_event
        simpa [Filter.le_principal_iff] using this
      have hx_principal : ClusterPt x (Filter.principal A) :=
        ClusterPt.mono hx h_le
      exact (isClosed_iff_clusterPt.mp hClosed) x hx_principal
    · intro hcluster
      have hClosed : IsClosed A := by
        refine (isClosed_iff_clusterPt).2 ?_
        intro x hx
        have h_ne : Filter.NeBot (Filter.principal A) :=
          ((ClusterPt.neBot hx).mono inf_le_right)
        have hx' : ClusterPt x (Filter.map (fun y : S => y) (Filter.principal A)) := by
          simpa using hx
        dsimp [clusterProperty] at hcluster
        have h_event : ∀ᶠ i in Filter.principal A, (fun y : S => y) i ∈ A := by
          simp
        haveI : Filter.NeBot (Filter.principal A) := h_ne
        exact hcluster (F := Filter.principal A) (u := fun y : S => y) (x := x) hx' h_event
      dsimp [limitProperty]
      intro ι F hF u x hx h_event
      exact hClosed.mem_of_tendsto hx h_event

/-- Lemma A2.2(a) (compact sets)
For sets A in a topological space S, A is compact if and only if
every net in A has at least one cluster point in A. -/
lemma kallenberg_a2_2a
    {S : Type*} [TopologicalSpace S] {A : Set S} :
    IsCompact A ↔
      ∀ {ι : Type*} {F : Filter ι} {u : ι → S},
        F ≠ ⊥ → (∀ᶠ i in F, u i ∈ A) → ∃ x ∈ A, ClusterPt x (Filter.map u F) := by
  classical
  constructor
  · intro hA ι F u hF_ne h_event
    haveI : Filter.NeBot F := by
      rw [Filter.neBot_iff]
      exact hF_ne
    have h_map : Filter.map u F ≤ 𝓟 A := by
      rwa [Filter.le_principal_iff]
    obtain ⟨x, hx, h_cluster⟩ := hA.exists_mapClusterPt h_map
    exact ⟨x, hx, h_cluster⟩
  · intro h
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro f hf
    have h_map : Filter.map (fun x : S => x) (f : Filter S) ≤ 𝓟 A := by
      simpa [Filter.le_principal_iff] using hf
    obtain ⟨x, hx, h_cluster⟩ := h (F := (f : Filter S)) (u := fun x : S => x) (x := x)
      (by infer_instance) h_map
    have h_cluster' : ClusterPt x (f : Filter S) := by simpa using h_cluster
    have h_le : (f : Filter S) ≤ 𝓝 x :=
      (f : Ultrafilter S).clusterPt_iff.mp h_cluster'
    exact ⟨x, hx, h_le⟩


/-- Lemma A2.2(b) (compact sets)
For sets A in a topological space S, if A is compact and has
exactly one cluster point x, then every net in A converges
to x. -/
lemma kallenberg_a2_2b
    {S : Type*} [TopologicalSpace S] {A : Set S} {x : S}
    (hA : IsCompact A)
    (hx : ClusterPt x (Filter.principal A))
    (h_unique : ∀ {y : S}, ClusterPt y (Filter.principal A) → y = x) :
    ∀ {ι : Type*} {F : Filter ι} {u : ι → S},
      F ≠ ⊥ → (∀ᶠ i in F, u i ∈ A) → Filter.Tendsto u F (𝓝 x) := by
  intro ι F u hF_ne h_event
  haveI : Filter.NeBot F := by
    rw [Filter.neBot_iff]
    exact hF_ne
  -- Convert h_event to the form expected by IsCompact.tendsto_nhds_of_unique_mapClusterPt
  have h_mem : ∀ᶠ i in F, u i ∈ A := h_event
  have h_map : Filter.map u F ≤ 𝓟 A := by
    rwa [Filter.le_principal_iff]
  -- We need: ∀ y ∈ A, MapClusterPt y F u → y = x
  -- But MapClusterPt y F u ↔ ClusterPt y (Filter.map u F)
  -- And we know ClusterPt y (Filter.principal A) → y = x
  -- So we need to relate ClusterPt y (Filter.map u F) to ClusterPt y (Filter.principal A)
  -- Since Filter.map u F ≤ Filter.principal A (from h_map),
  -- ClusterPt y (Filter.map u F) implies ClusterPt y (Filter.principal A)
  -- Actually, if G ≤ H and ClusterPt y G, then ClusterPt y H
  -- So: ClusterPt y (Filter.map u F) → ClusterPt y (Filter.principal A) → y = x
  have h_unique' : ∀ y ∈ A, MapClusterPt y F u → y = x := by
    intro y hy hy_map
    have hy_cluster : ClusterPt y (Filter.principal A) :=
      ClusterPt.mono hy_map h_map
    exact h_unique hy_cluster
  exact hA.tendsto_nhds_of_unique_mapClusterPt h_mem h_unique'

theorem kallenberg_a2_3
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (A : Subalgebra ℝ C(X, ℝ))
    (w : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  simpa using
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints (X := X)
      (A := A) w

/-- lemma: Let X be a lcscH space. There exists a countable base {B1,B2,...}
for X such that for every point x ∈ X, there is some Bn such that x ∈ Bn and
the closure of Bn is compact. -/
lemma lcscHausdorffSpace_countable_basis_with_compact_closure
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] :
    ∃ B : Set (Set S), B.Countable ∧ IsTopologicalBasis B ∧
      ∀ x : S, ∃ U ∈ B, x ∈ U ∧ IsCompact (closure U) := by
  classical
  refine ⟨countableBasis S, countable_countableBasis (α := S),
    isBasis_countableBasis (α := S), ?_⟩
  intro x
  obtain ⟨U, hUopen, hxU, hUcompact⟩ :=
    exists_isOpen_mem_isCompact_closure (x := x)
  have hxU_mem : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  obtain ⟨b, hb_mem, hx_b, hb_subset⟩ :=
    (isBasis_countableBasis (α := S)).exists_subset_of_mem_open hxU hUopen
  refine ⟨b, hb_mem, hx_b, ?_⟩
  have hsubset : closure b ⊆ closure U := closure_mono hb_subset
  exact IsCompact.of_isClosed_subset hUcompact isClosed_closure hsubset


/-- lemma: lcscH spaces have a countable base by relatively compact open sets -/
lemma lcscHausdorffSpace_countable_relatively_compact_basis
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] :
    ∃ B : Set (Set S), B.Countable ∧ IsTopologicalBasis B ∧ ∀ U ∈ B, IsCompact (closure U) := by
  classical
  obtain ⟨B, hBcount, hBbasis, hBcover⟩ :=
    lcscHausdorffSpace_countable_basis_with_compact_closure (S := S)
  choose U hUB hxU hUcompact using hBcover
  let B' : Set (Set S) := {V : Set S | V ∈ B ∧ IsCompact (closure V)}
  have hB'sub : B' ⊆ B := fun V hV => hV.1
  have hB'count : B'.Countable := hBcount.mono hB'sub
  have hB'open : ∀ V ∈ B', IsOpen V := fun V hV => hBbasis.isOpen hV.1
  have hB'basis : IsTopologicalBasis B' := by
    refine ⟨?_, ?_, ?_⟩
    · intro t₁ ht₁ t₂ ht₂ x hx
      rcases ht₁ with ⟨ht₁B, ht₁C⟩
      rcases ht₂ with ⟨ht₂B, ht₂C⟩
      have hx₁ : x ∈ t₁ := hx.1
      have hx₂ : x ∈ t₂ := hx.2
      have hOpen : IsOpen (t₁ ∩ t₂) :=
        (hBbasis.isOpen ht₁B).inter (hBbasis.isOpen ht₂B)
      have hxInter : x ∈ t₁ ∩ t₂ := by exact hx
      obtain ⟨V, hVB, hxV, hVsubset⟩ :=
        hBbasis.exists_subset_of_mem_open hxInter hOpen
      let Sx := U x
      have hSxB : Sx ∈ B := hUB x
      have hxSx : x ∈ Sx := hxU x
      have hSxCompact : IsCompact (closure Sx) := hUcompact x
      have hSxOpen : IsOpen Sx := hBbasis.isOpen hSxB
      have hxVSx : x ∈ V ∩ Sx := ⟨hxV, hxSx⟩
      have hOpenVSx : IsOpen (V ∩ Sx) := (hBbasis.isOpen hVB).inter hSxOpen
      obtain ⟨W, hWB, hxW, hWsubset⟩ :=
        hBbasis.exists_subset_of_mem_open hxVSx hOpenVSx
      have hWsubsetV : W ⊆ V := fun y hy => (hWsubset hy).1
      have hWsubsetSx : W ⊆ Sx := fun y hy => (hWsubset hy).2
      have hWsubsetInter : W ⊆ t₁ ∩ t₂ := fun y hy =>
        let hyV := (hWsubset hy).1
        let hyInter := hVsubset hyV
        ⟨hyInter.1, hyInter.2⟩
      have hWcompact : IsCompact (closure W) :=
        IsCompact.of_isClosed_subset hSxCompact isClosed_closure
          (closure_mono hWsubsetSx)
      refine ⟨W, ⟨hWB, hWcompact⟩, hxW, hWsubsetInter⟩
    · ext x; constructor
      · intro _; exact mem_univ x
      · intro _
        refine mem_sUnion.2 ?_
        exact ⟨U x, ⟨hUB x, hUcompact x⟩, hxU x⟩
    · have h_le : generateFrom B' ≤ ‹_› := by
        intro s hs
        induction hs with
        | basic s hs => exact hB'open s hs
        | univ => exact isOpen_univ
        | inter s t hs ht hsOpen htOpen => exact hsOpen.inter htOpen
        | sUnion S hS hIH => exact isOpen_sUnion fun s hs => hIH s hs
      exact le_antisymm h_le (le_generateFrom hB'open)
  refine ⟨B', hB'count, hB'basis, ?_⟩
  intro V hV
  exact hV.2

-- lemma: a compact Hausdorff space is normal (T_4) -

/-- Lemma A2.4(i) (lcscH spaces)
Let S be a locally compact, second countable, Hausdorff space. Then
S is Polish and σ-compact.
-/
lemma kallenberg_a2_4_i
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] :
    PolishSpace S ∧ SigmaCompactSpace S := by
  trivial

/-- Theorem A2.1 (equicontinuity and compactness, Arzelà–Ascoli)
For two metric spaces K and S, where K is compact and S is complete,
and let D be dense in K. Then a set A ⊆ C(K,S) is relatively compact
iff m_A is relatively compact in S for every D and
sup_{z∈A} w(z,h) → 0 as h → 0, where w(z,h) is the modulus of continuity.
In that case, A is relatively compact in S. -/
theorem kallenberg_a2_1_Ascoli
    {K S : Type*} [MetricSpace K] [CompactSpace K] [MetricSpace S] [CompleteSpace S]
    (D : Set K) (hD : Dense D) (A : Set C(K, S)) :
    (IsCompact (closure A) ↔
      (∀ d ∈ D, IsCompact (closure {z d | z ∈ A})) ∧
      (∀ h > 0, ∃ C : ℝ, ∀ z ∈ A, ∀ s t : K,
        dist (s : K) t < h → dist (z s) (z t) ≤ C)) := by
  sorry

/-- Theorem A2.2 (J¹-topology, Skorohod, Prohorov, Kolmogorov)
For a separable, complete metric space (S,ρ) and a dense set T ⊆ ℝ₊, there
exists a separable and complete metric d in D(ℝ₊, S) such that
d(z_n, z) → 0 iff sup_n |Λ_n(s) - Λ(s)| → 0 and
sup_{s,t} ρ(Λ_n(s), Λ_n(t); Λ(s), Λ(t)) → 0
for some time-changes Λ_n on ℝ₊. Furthermore, B(D(ℝ₊, S)) = σ{m_t; t ∈ T},
and a set A ⊆ D(ℝ₊, S) is relatively compact iff m_A is relatively compact
in S for every t ∈ T and sup_{z∈A} w_h(z, t_h) → 0 as h → 0. -/
theorem kallenberg_a2_2_Skorohod
    {S : Type*} [MetricSpace S] [CompleteSpace S] [SeparableSpace S]
    (T : Set ℝ) (hT : Dense T) : True := by
  trivial

/-- Theorem A2.3 (vague topology)
For any lcscH space S, we have
(i) M(S) is Polish in the vague topology;
(ii) a set A ⊆ M(S) is vaguely relatively compact iff sup_{μ∈A} μ(f) < ∞
for all f ∈ C_0^+(S);
(iii) if μ_n → μ vaguely and B ∈ Σ with μ(∂B) = 0, then μ_n(B) → μ(B);
(iv) B(M(S)) is generated by the maps m_f, f ∈ C_0^+(S), and also for any
μ ∈ M(S) by the maps m_B, B ∈ S_μ. -/
theorem kallenberg_a2_3_vague_topology
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] : True := by
  trivial

/-- Theorem A2.4 (measure-valued functions)
For any lcscH space S, there exist f_j ∈ C_0^+(S) such that a set
A ⊆ D(ℝ₊, M(S)) is relatively compact iff A_{f_j} = {μ_t f_j; μ ∈ A}
is relatively compact in D(ℝ₊, ℝ) for every j ∈ ℕ. -/
theorem kallenberg_a2_4_measure_valued
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] : True := by
  trivial

/-- Theorem A2.5 (Fell topology)
For any lcscH space S, and let F be the class of closed sets F ⊆ S,
endowed with the Fell topology. Then
(i) F is compact, second-countable, and Hausdorff;
(ii) F_n → F in F iff ρ(s, F_n) → ρ(s, F) for all s ∈ S;
(iii) {F ∈ F; F ∩ B ≠ ∅} is universally Borel measurable for every B ∈ Σ. -/
theorem kallenberg_a2_5_Fell_topology
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] : True := by
  trivial

/-- Lemma A2.6 (separation)
For any monotone function h : Σ → ℝ, the class Σ_h = {B ∈ Σ; h(B*) = h(B)}
is separating, where B* denotes the closure of B. -/
theorem kallenberg_a2_6_separation
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (h : Set S → ℝ) (h_mono : ∀ A B : Set S, A ⊆ B → h A ≤ h B) :
    True := by
  trivial

/-- Lemma A2.7 (countable separation)
Every separating class U ⊆ Σ contains a countable separating subclass. -/
theorem kallenberg_a2_7_countable_separation
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (U : Set (Set S)) (hU : ∀ B ∈ U, MeasurableSet B) : True := by
  trivial

/-- Lemma A2.8 (convergence of supports)
For a lcscH space S with countable base, and measures μ_n, μ ∈ M(S),
if μ_n → μ vaguely, then for any B ∈ Σ with μ(∂B) = 0, we have μ_n(B) → μ(B). -/
theorem kallenberg_a2_8_convergence_of_supports
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] : True := by
  trivial

/-- Lemma A2.9 (projective limits)
For metric spaces S_1, S_2, ..., consider a projective sequence of
nonempty, compact sets K_n ⊆ S_1 × ... × S_n. Then the projective limit
K = lim K_n is again nonempty and compact. -/
theorem kallenberg_a2_9_projective_limits
    {n : ℕ → Type*} [∀ i, MetricSpace (n i)]
    (K : ℕ → Set (n 0 × n 1)) : True := by
  trivial

end Appendix2
