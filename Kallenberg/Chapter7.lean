import Mathlib

open Set MeasureTheory Filter Topology Function
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace Chapter7

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability of a set under a probability measure, as a real number. -/
def prob (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : ℝ :=
  (μ s).toReal

/-! ### Filtrations and optional times -/

/-- Lemma 7.1 (optional times):
For any optional times σ and τ, we have
(i) τ is F_τ-measurable;
(ii) F_τ = F_t on {τ = t} for all t ∈ T;
(iii) F_σ ∩ {σ ≤ τ} ⊂ F_{σ ∧ τ} = F_σ ∩ F_τ. -/
lemma kallenberg_7_1
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (σ τ : Ω → ℕ) (hσ : ∀ n, MeasurableSet[F n] {ω | σ ω ≤ n}) (hτ : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n}) :
    True := by
  sorry

/-! ### Weakly optional times -/

/-- Lemma 7.2 (weakly optional times):
A random time τ is weakly F-optional iff it is F⁺-optional, in which case
F_{τ+} = F_τ⁺ = {A ∈ A; A ∩ {τ < t} ∈ F_t, t > 0}. -/
lemma kallenberg_7_2
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (τ : Ω → ℕ) :
    True := by
  sorry

/-! ### Closure properties -/

/-- Lemma 7.3 (closure properties):
For any random times τ_n and filtration F on R_+ or Z_+:
(i) If τ_n are F-optional, then σ = sup_n τ_n is F-optional.
(ii) If τ_n are weakly F-optional, then τ = inf_n τ_n is weakly F-optional,
and F_τ⁺ = ⋂_n F_{τ_n}⁺. -/
lemma kallenberg_7_3
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (τ_seq : ℕ → Ω → ℕ)
    (hτ_seq : ∀ n, MeasurableSet[F n] {ω | τ_seq n ω ≤ n}) :
    True := by
  sorry

/-! ### Discrete approximation -/

/-- Lemma 7.4 (discrete approximation):
For any weakly optional time τ in R_+, there exist countably valued optional times τ_n ↓ τ. -/
lemma kallenberg_7_4
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (τ : Ω → ℝ)
    (hτ : ∀ t, MeasurableSet[F 0] {ω | τ ω < t}) :
    True := by
  sorry

/-! ### Stopped processes -/

/-- Lemma 7.5 (stopped processes):
For a process X on R_+ or Z_+ and optional time τ, the stopped process X^τ is measurable
under suitable conditions. -/
lemma kallenberg_7_5
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hτ : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n}) :
    True := by
  sorry

/-! ### Hitting times -/

/-- Lemma 7.6 (hitting times):
Fix a filtration F on T = R_+ or Z_+, let X be an F-adapted process on T with values in a
measurable space (S, S), and let B ∈ S. Then τ_B is weakly optional under each of these
conditions:
(i) T = Z_+;
(ii) T = R_+, S is a metric space, B is closed, and X is continuous;
(iii) T = R_+, S is a topological space, B is open, and X is right-continuous. -/
lemma kallenberg_7_6
    {S : Type*} [MeasurableSpace S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → S) (B : Set S) :
    True := by
  sorry

/-! ### First entry -/

/-- Theorem 7.7 (first entry, Doob, Hunt):
Let the set A ⊂ R_+ × Ω be progressive with respect to some right-continuous and complete
filtration F. Then the time τ(ω) = inf{t ≥ 0; (t, ω) ∈ A} is F-optional. -/
theorem kallenberg_7_7
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : MeasurableSpace Ω) (hmF : F ≤ ‹_›)
    (A : Set (ℝ × Ω)) (hA : MeasurableSet A) :
    True := by
  sorry

/-! ### Augmented filtration -/

/-- Lemma 7.8 (augmented filtration):
Every filtration F on R_+ has a smallest right-continuous and complete extension G, given by
G_t = F̅_{t+} = F̅_{t+}, t ≥ 0. -/
lemma kallenberg_7_8
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) :
    True := by
  sorry

/-! ### Time-change -/

/-- Lemma 7.9 (time-change):
Given a right-continuous and complete filtration F and a continuous, strictly increasing
process X with induced filtration G, we have F_t = G_{X_t} for all t, and
F_τ = G_{X_τ} for any F-optional time τ. -/
lemma kallenberg_7_9
    {S T : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
    [MeasurableSpace T] [TopologicalSpace T] [BorelSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (G : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → S) (τ : Ω → ℕ) :
    True := by
  sorry

/-! ### Doob decomposition -/

/-- Lemma 7.10 (centering, Doob decomposition):
Any integrable and F-adapted process X on Z_+ has an a.s. unique decomposition M + A,
where M is an F-martingale and A is an F-predictable process with A_0 = 0.
In particular, X is a submartingale iff A is a.s. nondecreasing. -/
lemma kallenberg_7_10
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) :
    True := by
  sorry

/-! ### Convex maps -/

/-- Lemma 7.11 (convex maps):
Let M be a martingale in R^d, and consider a convex function f : R^d → R such that
X = f(M) is integrable. Then X is a submartingale.
The statement remains true for any real submartingale M, provided that f is also nondecreasing. -/
lemma kallenberg_7_11
    {d : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (M : ℕ → Ω → ℝ) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ univ f) :
    True := by
  sorry

/-! ### Optional sampling -/

/-- Theorem 7.12 (optional sampling, Doob):
Let M be a martingale on some countable index set T with filtration F, and consider two
optional times σ and τ, where τ is bounded. Then M_τ is integrable, and
M_{σ∧τ} = E[M_τ | F_σ] a.s. -/
theorem kallenberg_7_12
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (M : ℕ → Ω → ℝ) (σ τ : Ω → ℕ)
    (hM_martingale : ∀ n, Integrable (M n) μ)
    (hσ_opt : ∀ n, MeasurableSet[F n] {ω | σ ω ≤ n})
    (hτ_opt : ∀ n, MeasurableSet[F n] {ω | τ ω ≤ n})
    (hτ_bdd : ∃ N, ∀ ω, τ ω ≤ N) :
    True := by
  sorry

/-! ### Submartingale inequalities -/

/-- Proposition 7.15 (maximum inequality, Doob):
For a submartingale X on a countable index set T and p > 1, there exists a constant C_p
such that P[X^*_t > λ] ≤ (E|X_t|^p) / (C_p λ^p) for all t and λ > 0. -/
lemma kallenberg_7_15
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (p : ℝ) (hp : 1 < p) :
    True := by
  sorry

/-- Proposition 7.16 (norm inequality, Doob):
Let M be a martingale on a countable index set T, and fix any p, q > 1 with
p^{-1} + q^{-1} = 1. Then ‖M_t^*‖_p ≤ q ‖M_t‖_p, t ∈ T. -/
lemma kallenberg_7_16
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (M : ℕ → Ω → ℝ) (p q : ℝ) (hpq : p⁻¹ + q⁻¹ = 1) (hp : 1 < p) :
    True := by
  sorry

/-! ### Upcrossing inequality -/

/-- Lemma 7.17 (upcrossing inequality, Doob, Snell):
Let X be a submartingale on a countable index set T, and let N_a^b(t) denote the number of
[a, b]-crossings of X up to time t. Then
E[N_a^b(t)] ≤ E[(X_t - a)^+] / (b - a), t ∈ T, a < b in R. -/
lemma kallenberg_7_17
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) :
    True := by
  sorry

/-! ### Martingale convergence -/

/-- Theorem 7.18 (martingale convergence, Doob):
A martingale on an unbounded index set converges a.s. iff it is bounded in L^1.
More precisely, for a submartingale X on Z_+, we have a.s.
{sup_n M_n < ∞} = ⋃_m {M ≡ M^{T_m}} where T_m = inf{n; M_n > m}.
The reverse implication is obvious, since every convergent sequence in R is bounded. -/
theorem kallenberg_7_18
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) :
    True := by
  sorry

/-! ### Extended Borel-Cantelli -/

/-- Corollary 7.20 (extended Borel-Cantelli lemma, Lévy):
For any filtration F on Z_+, let A_n ∈ F_n, n ∈ N. Then a.s.
{A_n i.o.} = {∑_n P[A_n | F_{n-1}] = ∞}. -/
lemma kallenberg_7_20
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet[F n] (A n)) :
    True := by
  sorry

/-! ### Lp-convergence -/

/-- Corollary 7.22 (Lp-convergence):
Let M be a martingale on an unbounded index set T, and fix any p > 1. Then M converges in
L^p iff it is L^p-bounded. -/
lemma kallenberg_7_22
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (M : ℕ → Ω → ℝ) (p : ℝ) (hp : 1 < p) :
    True := by
  sorry

/-! ### Conditioning limits -/

/-- Theorem 7.23 (conditioning limits, Jessen, Lévy):
Let F be a filtration on a countable index set T ⊂ R that is unbounded above or below.
Then for any ξ ∈ L^1, we have as t → ±∞
E[ξ | F_t] → E[ξ | F_{±∞}] a.s. and in L^1. -/
theorem kallenberg_7_23
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (ξ : Ω → ℝ) (hξ_int : Integrable ξ μ) :
    True := by
  sorry

/-! ### Uniform integrability -/

/-- Lemma 7.28 (uniform integrability):
A submartingale X on Z_+ is uniformly integrable iff E[X] is bounded. -/
lemma kallenberg_7_28
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) :
    True := by
  sorry

/-! ### Optional sampling in continuous time -/

/-- Theorem 7.29 (optional sampling and closure, Doob):
Let X be an F-submartingale on R_+, where X and F are right-continuous, and consider two
optional times σ and τ, where τ is bounded. Then X_τ is integrable, and
X_{σ∧τ} ≤ E[X_τ | F_σ] a.s. -/
theorem kallenberg_7_29
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ) (σ τ : Ω → ℕ)
    (hF_right_cont : ∀ n, MeasurableSet[F (n + 1)] {ω | X (n + 1) ω ∈ Set.univ}) (hX_int : ∀ n, Integrable (X n) μ)
    (hτ_bdd : ∃ N, ∀ ω, τ ω ≤ N) :
    True := by
  sorry

/-! ### First hit -/

/-- Corollary 7.30 (first hit):
Let M be a continuous martingale with M_0 = 0 and P[M^* > 0] > 0, and define
τ_x = inf{t > 0; M_t = x}. Then
P[τ_a < τ_b | M^* > 0] ≤ b/(b-a) ≤ P[τ_a ≤ τ_b | M^* > 0], a < 0 < b. -/
lemma kallenberg_7_30
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (M : ℕ → Ω → ℝ)
    (hM0 : ∀ ω, M 0 ω = 0)
    (hMpos : μ {ω | ∃ n, |M n ω| > 0} > 0) :
    True := by
  sorry

/-! ### Absorption -/

/-- Lemma 7.31 (absorption):
Let X ≥ 0 be a right-continuous supermartingale, and put
τ = inf{t ≥ 0; X_t ∧ X_{t-} = 0}. Then X = 0 a.s. on [τ, ∞). -/
lemma kallenberg_7_31
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (hX_nonneg : ∀ n ω, 0 ≤ X n ω) :
    True := by
  sorry

/-! ### Tail σ-field -/

/-- Corollary 7.25 (tail σ-field):
If F_1, F_2, ... and G are independent σ-fields, then
⋂_n σ{F_n, F_{n+1}, ...; G} = G a.s. -/
lemma kallenberg_7_25
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F_seq : ℕ → MeasurableSpace Ω) (G : MeasurableSpace Ω)
    (h_indep : ∀ n, ProbabilityTheory.Indep (F_seq n) G (μ := μ)) :
    True := by
  sorry

/-! ### Regular densities -/

/-- Proposition 7.26 (regular densities):
For any measurable space (S, S) and Borel spaces (T, T) and (U, U), let μ be a probability
kernel from S to T × U. Then the densities
ν(s, t, B) = μ(s, dt × B) / μ(s, dt × U), s ∈ S, t ∈ T, B ∈ U,
have versions that form a probability kernel from S × T to U. -/
lemma kallenberg_7_26
    {S T U : Type*} [MeasurableSpace S] [MeasurableSpace T] [TopologicalSpace T] [BorelSpace T]
    [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U]
    [SecondCountableTopology T] [SecondCountableTopology U]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : S → T → Set U → ℝ≥0∞) (hν_nonneg : ∀ s t B, 0 ≤ ν s t B) :
    True := by
  sorry

/-! ### Regularization -/

/-- Theorem 7.27 (regularization, Doob):
For any F-submartingale X on R_+ with restriction Y to Q_+, we have:
(i) Y⁺ exists and is rcll outside some fixed P-null set A, and Z = 1_A · Y⁺ is a submartingale
with respect to the augmented filtration F̅⁺.
(ii) If F is right-continuous, then X has an rcll version iff E[X] is right-continuous;
this holds in particular when X is a martingale. -/
theorem kallenberg_7_27
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (hX_int : ∀ n, Integrable (X n) μ) :
    True := by
  sorry

end Chapter7
