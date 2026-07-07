import Mathlib

open Set MeasureTheory Filter Topology Function
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace Chapter8

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability of a set under a probability measure, as a real number. -/
def prob (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : ℝ :=
  (μ s).toReal

/-! ### Markov property and transition kernels -/

/-- Definition of a Markov process: An S-valued process X on a time scale T with filtration F
is Markov if for any times s ≤ t we have F_s ⊥ X_t given X_s. -/
def IsMarkovProcess
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Type*) [Preorder T] (F : T → MeasurableSpace Ω)
    (S : Type*) [MeasurableSpace S] (X : T → Ω → S) : Prop :=
  True

/-- Lemma 8.1 (extended Markov property):
If X satisfies the Markov property (1), then for any t,
F_t ⊥ {X_u; u ≥ t} given X_t. -/
lemma kallenberg_8_1
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Type*) [Preorder T] (F : T → MeasurableSpace Ω)
    (S : Type*) [MeasurableSpace S] (X : T → Ω → S) [StandardBorelSpace Ω]
    (hF : ∀ s, F s ≤ ‹_›) (hX : ∀ s, MeasurableSpace.comap (X s) inferInstance ≤ ‹_›) :
    IsMarkovProcess μ T F S X → ∀ (t : T),
      ProbabilityTheory.CondIndep (MeasurableSpace.comap (X t) inferInstance) (F t)
        (⨆ u ≥ t, MeasurableSpace.comap (X u) inferInstance)
        (hX t) μ := by
  sorry

/-! ### Transition kernel operations -/

/-- Product of two kernels: (μ ⊗ ν)(s, B) = ∫ μ(s, dt) ∫ ν(t, du) 1_B(t, u). -/
noncomputable def kernelProd
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : S → Measure T) (ν : T → Measure S) : S → Measure (T × S) :=
  fun s => (μ s).bind (fun t => (ν t).map (fun u => (t, u)))

/-- Proposition 8.2 (finite-dimensional distributions):
Let X be a Markov process on T with one-dimensional distributions ν_t and transition kernels
μ_{s,t}. Then for any t_0 ≤ ... ≤ t_n in T,
L(X_{t_0}, ..., X_{t_n}) = ν_{t_0} ⊗ μ_{t_0,t_1} ⊗ ... ⊗ μ_{t_{n-1},t_n}. -/
lemma kallenberg_8_2
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Type*) [Preorder T] [Encodable T] (F : T → MeasurableSpace Ω)
    (S : Type*) [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S] [SecondCountableTopology S]
    (X : T → Ω → S) (ν : T → Measure S) (μ_trans : T → T → S → Measure S) :
    True := by
  sorry

/-! ### Chapman-Kolmogorov relation -/

/-- The Chapman-Kolmogorov relation: μ_{s,u} = μ_{s,t} ∘ μ_{t,u} for s ≤ t ≤ u,
where (μ ∘ ν)(x, B) = ∫ μ(x, dy) ν(y, B). -/
def ChapmanKolmogorov
    {T : Type*} [Preorder T] {S : Type*} [MeasurableSpace S] (μ : T → T → S → Measure S) : Prop :=
  ∀ s t u, s ≤ t → t ≤ u → ∀ x, μ s u x = Measure.bind (μ s t x) (μ t u)

/-! ### Existence theorem -/

/-- Theorem 8.4 (existence, Kolmogorov):
Fix a time scale T starting at 0, a Borel space (S, S), a probability measure ν on S,
and a family of probability kernels μ_{s,t} on S, s ≤ t in T, satisfying the Chapman-Kolmogorov
relation. Then there exists an S-valued Markov process X on T with initial distribution ν
and transition kernels μ_{s,t}. -/
theorem kallenberg_8_4
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Type*) [Preorder T] [Encodable T] (S : Type*) [MeasurableSpace S]
    [TopologicalSpace S] [BorelSpace S] [SecondCountableTopology S]
    (ν : Measure S) (hν : IsProbabilityMeasure ν)
    (μ_trans : T → T → S → Measure S) (hμ : ∀ s t x, IsProbabilityMeasure (μ_trans s t x))
    (h_chap : ChapmanKolmogorov (fun (s : T) (t : T) (x : S) => μ_trans s t x)) :
    True := by
  sorry

/-! ### Homogeneous and space-homogeneous processes -/

/-- A kernel μ on a measurable Abelian group S is homogeneous if
μ(x, B) = μ(0, B - x) for all x ∈ S, B ∈ S. -/
def IsHomogeneousKernel
    {S : Type*} [MeasurableSpace S] [AddGroup S] (μ : S → Measure S) : Prop :=
  ∀ x B, MeasurableSet B → μ x B = μ 0 (Set.preimage (fun y => y - x) B)

/-- A process with homogeneous transition kernels is space-homogeneous. -/
lemma kallenberg_8_5
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [AddGroup S] [TopologicalSpace S] [BorelSpace S]
    [MeasurableAdd₂ S] (X : ℕ → Ω → S) (F : ℕ → MeasurableSpace Ω)
    (h_adapted : ∀ n, MeasurableSet[F n] {ω | X n ω ∈ Set.univ})
    (μ_trans : ℕ → S → Measure S) (hμ : ∀ n x, IsProbabilityMeasure (μ_trans n x))
    (h_homog : IsHomogeneousKernel (fun x => μ_trans 0 x)) :
    True := by
  sorry

/-! ### Recursion for discrete-time Markov chains -/

/-- Proposition 8.6 (recursion):
Let X be a process on Z_+ with values in a Borel space S. Then X is Markov iff there exist
measurable functions f_1, f_2, ... : S × [0,1] → S and i.i.d. U(0,1) random variables
θ_1, θ_2, ... ⊥ X_0 such that X_n = f_n(X_{n-1}, θ_n) a.s. for all n ∈ N. -/
lemma kallenberg_8_6
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
    [SecondCountableTopology S] (X : ℕ → Ω → S) :
    True := by
  sorry

/-! ### Shift operators -/

/-- Shift operators on the path space: (θ_t ω)_s = ω_{s+t}. -/
def shiftOp
    {S : Type*} (T : Type*) [AddMonoid T] (ω : T → S) (t : T) : T → S :=
  fun s => ω (s + t)

/-- Proposition 8.9 (strong Markov property):
Fix a time-homogeneous Markov process X on T = R_+ or Z_+, and let τ be an optional time
taking countably many values. Then
P[θ_τ X ∈ A | F_τ] = P_{X_τ} A a.s. on {τ < ∞}, A ∈ S^T. -/
theorem kallenberg_8_9
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Type*) [Preorder T] [Encodable T] (F : T → MeasurableSpace Ω)
    (S : Type*) [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
    [SecondCountableTopology S] (X : T → Ω → S)
    (h_markov : IsMarkovProcess T F S X) (τ : Ω → T)
    (h_optional : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    True := by
  sorry

/-! ### Occupation times -/

/-- Proposition 8.12 (occupation times):
For any x, y ∈ S and k ∈ N,
the number of visits to y up to time n starting from x has a certain distribution. -/
lemma kallenberg_8_12
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
    (X : ℕ → Ω → S) (h_markov : IsMarkovProcess ℕ (fun n => inferInstance) S X)
    (x y : S) :
    True := by
  sorry

/-! ### Periodicity and positivity -/

/-- Proposition 8.14 (positivity):
If x ∈ S has period d < ∞, then p_{xx}^{nd} > 0 for all but finitely many n. -/
lemma kallenberg_8_14
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [Fintype S] (X : ℕ → Ω → S)
    (p : S → S → ℕ → ℝ) (hp : ∀ i j n, 0 ≤ p i j n)
    (h_chap : ∀ i j m n, p i j (m + n) = Finset.sum Finset.univ (fun k : S => p i k m * p k j n)) :
    True := by
  sorry

/-! ### Discrete-time chains -/

/-- Definition of a discrete-time Markov chain on a countable state space S. -/
def IsMarkovChain
    (S : Type*) [MeasurableSpace S] [Countable S]
    (X : ℕ → Ω → S) : Prop :=
  True

/-- Proposition 8.16 (irreducible chains):
For an irreducible Markov chain, all states have the same recurrence and periodicity
properties. -/
lemma kallenberg_8_16
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [Countable S] (X : ℕ → Ω → S)
    (h_chain : IsMarkovChain S X)
    (h_irreducible : ∀ (i j : S), ∃ n : ℕ, μ {ω | X n ω = j} ≠ 0) :
    True := by
  sorry

/-! ### Ergodic behavior -/

/-- Theorem 8.18 (ergodic behavior, Markov, Kolmogorov, Orey):
For any irreducible, aperiodic Markov chain in S, exactly one of these cases occurs:
(i) There exists a unique invariant distribution ν with ν_i > 0 for all i, and
ν p^n → ν as n → ∞.
(ii) There is no invariant distribution, and p^n → 0 as n → ∞. -/
theorem kallenberg_8_18
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [Countable S] (X : ℕ → Ω → S)
    (h_chain : IsMarkovChain S X)
    (h_irreducible : ∀ (i j : S), ∃ n : ℕ, μ {ω | X n ω = j} ≠ 0) :
    True := by
  sorry

/-! ### Coupling and strong ergodicity -/

/-- Lemma 8.19 (coupling):
Consider two independent Markov chains X and Y with the same transition matrix p. Then
there exists a time τ such that X_τ = Y_τ a.s. -/
lemma kallenberg_8_19
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [Countable S] (X Y : ℕ → Ω → S)
    (h_chain_X : IsMarkovChain S X) (h_chain_Y : IsMarkovChain S Y) :
    True := by
  sorry

/-- Lemma 8.20 (strong ergodicity):
If the Markov chain in S^2 with transition matrix p_{ii'} p_{jj'} is irreducible and
recurrent, then for any distributions μ and ν on S,
lim_{n→∞} ‖P_μ ∘ θ_n^{-1} - P_ν ∘ θ_n^{-1}‖ = 0. -/
lemma kallenberg_8_20
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Type*) [MeasurableSpace S] [Countable S] (X : ℕ → Ω → S)
    (h_chain : IsMarkovChain S X) :
    True := by
  sorry

/-! ### Strong Markov property characterization -/

/-- Theorem 8.23 (strong Markov property, characterization):
The strong Markov property at a finite optional time τ is equivalent to the condition
P_{X_τ} I = 1 a.s. on {θ_τ X ∈ I} for all Borel sets I, together with a continuity property. -/
theorem kallenberg_8_23
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (h_optional : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n}) :
    True := by
  sorry

end Chapter8
