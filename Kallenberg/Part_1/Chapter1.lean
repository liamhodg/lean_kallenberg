import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib


open Set MeasureTheory

variable {α : Type*}

namespace MeasureTheory

/-- `IsDynkinSystem s` says the collection of sets `s` is a Dynkin (λ-)system:
    it contains `∅`, is closed under complement, and under countable pairwise-disjoint unions. -/
def IsDynkinSystem (s : Set (Set α)) : Prop :=
  (∅ : Set α) ∈ s ∧
  (∀ ⦃A⦄, A ∈ s → Aᶜ ∈ s) ∧
  (∀ f : ℕ → Set α,
      Pairwise (Function.onFun Disjoint f) →
      (∀ n, f n ∈ s) →
      (⋃ n, f n) ∈ s)

namespace IsDynkinSystem

variable {s : Set (Set α)}

theorem has_empty (hs : IsDynkinSystem s) : (∅ : Set α) ∈ s := hs.1

theorem has_compl (hs : IsDynkinSystem s) {A : Set α} (hA : A ∈ s) : Aᶜ ∈ s :=
  hs.2.1 hA

theorem has_iUnion_nat (hs : IsDynkinSystem s)
    (f : ℕ → Set α)
    (hpair : Pairwise (Function.onFun Disjoint f))
    (hf : ∀ n, f n ∈ s) :
    (⋃ n, f n) ∈ s :=
  hs.2.2 f hpair hf

/-- Turn an `IsDynkinSystem` predicate into a bundled `DynkinSystem`. -/
def toDynkinSystem (hs : IsDynkinSystem s) : MeasurableSpace.DynkinSystem α :=
{ Has            := fun t => t ∈ s
, has_empty      := hs.has_empty
, has_compl      := by intro A hA; exact hs.has_compl hA
, has_iUnion_nat := by
    intro f hpair hf
    simpa using hs.has_iUnion_nat f hpair hf }

end IsDynkinSystem

/-- The underlying set of a bundled `DynkinSystem`. -/
def MeasurableSpace.DynkinSystem.carrier (d : MeasurableSpace.DynkinSystem α) :
    Set (Set α) :=
  {t | d.Has t}

/-- A bundled `DynkinSystem` satisfies the `IsDynkinSystem` predicate on its carrier. -/
theorem MeasurableSpace.DynkinSystem.isDynkinSystem
    (d : MeasurableSpace.DynkinSystem α) :
    IsDynkinSystem (d.carrier) :=
by
  refine ⟨d.has_empty, ?_, ?_⟩
  · intro A hA; simpa using d.has_compl hA
  · intro f hpair hf
    simpa using d.has_iUnion_nat (f := f) hpair hf

end MeasureTheory

namespace Chapter1

variable {S : Type*}

/-- A class C is a σ-field if and only if it is both
a π-system and a λ-system. -/
lemma sigma_is_pi
  {C : MeasurableSpace S} : IsPiSystem {A : Set S | MeasurableSet[C] A} := by
  refine (?h)
  intro A hA B hB _hABne
  simpa using hA.inter hB

lemma sigma_is_dynkin
  {C : MeasurableSpace S} : IsDynkinSystem {A : Set S | MeasurableSet[C] A} := by
  refine ⟨?h.has_empty, ?h2, ?h3⟩
  · simp [Set.mem_setOf_eq]
  · simp [Set.mem_setOf_eq]
  · intro f hpair hf
    have hf' : ∀ n, MeasurableSet[C] (f n) := by
      intro n; simpa [Set.mem_setOf_eq] using hf n
    simpa [Set.mem_setOf_eq] using (MeasurableSet.iUnion hf')




/-- Theorem 1.1 (monotone classes, Sierpinski):
For any π-system C and λ-system D in a space S,
we have C ⊆ D → σ(C) ⊆ D.
-/
theorem kallenberg_1_1
  {C : Set (Set S)} (hC : IsPiSystem C)
  (D : MeasurableSpace.DynkinSystem S) (hCD : ∀ s ∈ C, D.Has s) :
  ∀ {A : Set S}, MeasurableSet[MeasurableSpace.generateFrom C] A → D.Has A := by
  have h :=
    MeasurableSpace.induction_on_inter
      (m := MeasurableSpace.generateFrom C)
      (C := fun s _ => D.Has s)
      (s := C)
      (h_eq := rfl)
      (h_inter := hC)
      (empty := D.has_empty)
      (basic := fun t ht => hCD t ht)
      (compl := fun _ _ ht => D.has_compl ht)
      (iUnion :=
        fun f hpair _ hf =>
          D.has_iUnion_nat (f := f) hpair hf)
  intro A hA
  exact h A hA

/-- Lemma 1.2 (product σ-field):
For any separable metric spaces S₁,S₂,⋯, we
have B(S₁×S₂×⋯) = B(S₁)⊗B(S₂)⊗⋯ -/

lemma kallenberg_1_2
  {ι : Type*} [Countable ι] (S : ι → Type*)
  [∀ i, TopologicalSpace (S i)] [∀ i, MeasurableSpace (S i)]
  [∀ i, BorelSpace (S i)] [∀ i, SecondCountableTopology (S i)] :
  borel (∀ i, S i) = MeasurableSpace.pi := by
  let _ := Pi.borelSpace (X := S)
  simpa using (‹BorelSpace (∀ i, S i)›.measurable_eq).symm


/-- Lemma 1.3 (induced σ-fields):
For any mapping f between measurable spaces
S and T, we have
(i) Sp = f^{-1} T is a σ-field in S;
(ii) Tp = {B ⊆ T; f^{-1} B ∈ S} is a σ-field in T. -/

lemma kallenberg_1_3
  {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] (f : S → T) :
  IsDynkinSystem {A : Set S | MeasurableSet[MeasurableSpace.comap f inferInstance] A} ∧
    IsDynkinSystem {B : Set T | MeasurableSet[MeasurableSpace.map f inferInstance] B} := by
  constructor
  · simpa using (sigma_is_dynkin (C := MeasurableSpace.comap f inferInstance))
  · simpa using (sigma_is_dynkin (C := MeasurableSpace.map f inferInstance))


end Chapter1
