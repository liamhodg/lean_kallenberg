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
      sorry
  -- classical
  -- constructor
  -- · constructor
  --   · intro hA
  --     dsimp [limitProperty]
  --     intro ι F hF u x hx h_event
  --     haveI : Filter.NeBot F := hF
  --     exact hA.mem_of_tendsto hx h_event
  --   · intro hlimit
  --     refine (isClosed_iff_forall_filter).2 ?_
  --     intro x F hF hFA hFx
  --     have h_event : ∀ᶠ i in F, (fun y : S => y) i ∈ A := by
  --       have : A ∈ F := hFA (by simp)
  --       simpa using this
  --     have h_tend : Filter.Tendsto (fun y : S => y) F (𝓝 x) := by
  --       refine (Filter.tendsto_def).2 ?_
  --       intro s hs
  --       exact hFx hs
  --     dsimp [limitProperty] at hlimit
  --     haveI : Filter.NeBot F := hF
  --     exact hlimit (F := F) (u := fun y : S => y) (x := x) h_tend h_event
  -- · constructor
  --   · intro hlimit
  --     have hClosed : IsClosed A := by
  --       refine (isClosed_iff_forall_filter).2 ?_
  --       intro x F hF hFA hFx
  --       have h_event : ∀ᶠ i in F, (fun y : S => y) i ∈ A := by
  --         have : A ∈ F := hFA (by simp)
  --         simpa using this
  --       have h_tend : Filter.Tendsto (fun y : S => y) F (𝓝 x) := by
  --         refine (Filter.tendsto_def).2 ?_
  --         intro s hs
  --         exact hFx hs
  --       dsimp [limitProperty] at hlimit
  --       haveI : Filter.NeBot F := hF
  --       exact hlimit (F := F) (u := fun y : S => y) (x := x) h_tend h_event
  --     dsimp [clusterProperty]
  --     intro ι F _ u x hx h_event
  --     have h_le : Filter.map u F ≤ Filter.principal A := by
  --       have : A ∈ Filter.map u F := by
  --         simpa using h_event
  --       simpa [Filter.le_principal_iff] using this
  --     have hx_principal : ClusterPt x (Filter.principal A) :=
  --       ClusterPt.mono hx h_le
  --     exact (isClosed_iff_clusterPt.mp hClosed) x hx_principal
  --   · intro hcluster
  --     have hClosed : IsClosed A := by
  --       refine (isClosed_iff_clusterPt).2 ?_
  --       intro x hx
  --       have h_ne : Filter.NeBot (Filter.principal A) :=
  --         ((ClusterPt.neBot hx).mono inf_le_right)
  --       have hx' : ClusterPt x (Filter.map (fun y : S => y) (Filter.principal A)) := by
  --         simpa using hx
  --       dsimp [clusterProperty] at hcluster
  --       have h_event : ∀ᶠ i in Filter.principal A, (fun y : S => y) i ∈ A := by
  --         simp
  --       haveI : Filter.NeBot (Filter.principal A) := h_ne
  --       exact hcluster (F := Filter.principal A) (u := fun y : S => y) (x := x) hx' h_event
  --     dsimp [limitProperty]
  --     intro ι F hF u x hx h_event
  --     exact hClosed.mem_of_tendsto hx h_event

/-- Lemma A2.2(a) (compact sets)
For sets A in a topological space S, A is compact if and only if
every net in A has at least one cluster point in A. -/
lemma kallenberg_a2_2a
    {S : Type*} [TopologicalSpace S] {A : Set S} :
    IsCompact A ↔
      ∀ {ι : Type*} {F : Filter ι} {u : ι → S},
        F ≠ ⊥ → (∀ᶠ i in F, u i ∈ A) → ∃ x ∈ A, ClusterPt x (Filter.map u F) := by
  sorry


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
  sorry

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
    sorry
  -- classical
  -- obtain ⟨B, hBcount, hBbasis, hBcover⟩ :=
  --   lcscHausdorffSpace_countable_basis_with_compact_closure (S := S)
  -- choose U hUB hxU hUcompact using hBcover
  -- let B' : Set (Set S) := {V : Set S | V ∈ B ∧ IsCompact (closure V)}
  -- have hB'sub : B' ⊆ B := fun V hV => hV.1
  -- have hB'count : B'.Countable := hBcount.mono hB'sub
  -- have hB'open : ∀ V ∈ B', IsOpen V := fun V hV => hBbasis.isOpen hV.1
  -- have hB'basis : IsTopologicalBasis B' := by
  --   refine ⟨?_, ?_, ?_⟩
  --   · intro t₁ ht₁ t₂ ht₂ x hx
  --     rcases ht₁ with ⟨ht₁B, ht₁C⟩
  --     rcases ht₂ with ⟨ht₂B, ht₂C⟩
  --     have hx₁ : x ∈ t₁ := hx.1
  --     have hx₂ : x ∈ t₂ := hx.2
  --     have hOpen : IsOpen (t₁ ∩ t₂) :=
  --       (hBbasis.isOpen ht₁B).inter (hBbasis.isOpen ht₂B)
  --     have hxInter : x ∈ t₁ ∩ t₂ := by exact hx
  --     obtain ⟨V, hVB, hxV, hVsubset⟩ :=
  --       hBbasis.exists_subset_of_mem_open hxInter hOpen
  --     let Sx := U x
  --     have hSxB : Sx ∈ B := hUB x
  --     have hxSx : x ∈ Sx := hxU x
  --     have hSxCompact : IsCompact (closure Sx) := hUcompact x
  --     have hSxOpen : IsOpen Sx := hBbasis.isOpen hSxB
  --     have hxVSx : x ∈ V ∩ Sx := ⟨hxV, hxSx⟩
  --     have hOpenVSx : IsOpen (V ∩ Sx) := (hBbasis.isOpen hVB).inter hSxOpen
  --     obtain ⟨W, hWB, hxW, hWsubset⟩ :=
  --       hBbasis.exists_subset_of_mem_open hxVSx hOpenVSx
  --     have hWsubsetV : W ⊆ V := fun y hy => (hWsubset hy).1
  --     have hWsubsetSx : W ⊆ Sx := fun y hy => (hWsubset hy).2
  --     have hWsubsetInter : W ⊆ t₁ ∩ t₂ := fun y hy =>
  --       let hyV := (hWsubset hy).1
  --       let hyInter := hVsubset hyV
  --       ⟨hyInter.1, hyInter.2⟩
  --     have hWcompact : IsCompact (closure W) :=
  --       IsCompact.of_isClosed_subset hSxCompact isClosed_closure
  --         (closure_mono hWsubsetSx)
  --     refine ⟨W, ⟨hWB, hWcompact⟩, hxW, hWsubsetInter⟩
  --   · ext x; constructor
  --     · intro _; exact mem_univ x
  --     · intro _
  --       refine mem_sUnion.2 ?_
  --       exact ⟨U x, ⟨hUB x, hUcompact x⟩, hxU x⟩
  --   ·
  --     have h_le : generateFrom B' ≤ ‹_› := by
  --       intro s hs
  --       induction hs with
  --       | basic s hs => exact hB'open s hs
  --       | univ => exact isOpen_univ
  --       | inter s t hs ht hsOpen htOpen => exact hsOpen.inter htOpen
  --       | sUnion S hS hIH => exact isOpen_sUnion fun s hs => hIH s hs
  --     exact le_antisymm h_le (le_generateFrom hB'open)
  -- refine ⟨B', hB'count, hB'basis, ?_⟩
  -- intro V hV
  -- exact hV.2

-- lemma: a compact Hausdorff space is normal (T_4) -

/-- Lemma A2.4(i) (lcscH spaces)
Let S be a locally compact, second countable, Hausdorff space. Then
S is Polish and σ-compact.
-/
lemma kallenberg_a2_4_i
    (S : Type*) [TopologicalSpace S] [LcscHausdorffSpace S] :
    PolishSpace S ∧ SigmaCompactSpace S := by
  sorry


end Appendix2
