import Mathlib

open Set MeasureTheory Filter Topology Function
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace Chapter4

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probability of a set under a probability measure, as a real number. -/
def prob (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : ℝ :=
  (μ s).toReal

/-- Lemma 4.1 (moments and tails, Bienaymé, Chebyshev, Paley-Zygmund):
For ξ ≥ 0 with 0 < E[ξ] < ∞, we have
(1-r)²(E[ξ])² / E[ξ²] ≤ P[ξ > r E[ξ]] ≤ 1/r for r > 0,
and P[|ξ - E[ξ]| > ε] ≤ ε⁻² Var(ξ) for ε > 0. -/
lemma kallenberg_4_1
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω)
    (hξ_int : Integrable ξ μ) (hξ_sq_int : Integrable (fun ω => ξ ω ^ 2) μ) :
    (∀ r > 0, (1 - r) ^ 2 * ((∫ ω, ξ ω ∂μ) ^ 2) / (∫ ω, ξ ω ^ 2 ∂μ) ≤
      prob μ {ω | ξ ω > r * (∫ ω, ξ ω ∂μ)} ∧
      prob μ {ω | ξ ω > r * (∫ ω, ξ ω ∂μ)} ≤ 1 / r) ∧
    (∀ ε > 0, prob μ {ω | |ξ ω - (∫ ω, ξ ω ∂μ)| > ε} ≤
      ε ^ (-2 : ℝ) * (∫ ω, ((ξ ω - (∫ ω, ξ ω ∂μ)) ^ 2) ∂μ)) := by
  sorry

/-- Lemma 4.2 (subsequence criterion):
ξ_n → ξ in probability iff every subsequence has a further subsequence
such that ξ_n → ξ a.s. along that subsequence. -/
lemma kallenberg_4_2
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (ξ : Ω → S) (ξ_seq : ℕ → Ω → S) (hξ : Measurable ξ) (hξ_seq : ∀ n, Measurable (ξ_seq n)) :
    (∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω) (ξ ω) > ε}) Filter.atTop (𝓝 0)) ↔
    (∀ (N' : Set ℕ), N' ∈ Filter.cofinite → ∃ (N'' : Set ℕ), N'' ⊆ N' ∧ N'' ∈ Filter.cofinite ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ξ_seq n ω) Filter.atTop (𝓝 (ξ ω))) := by
  sorry

/-- Lemma 4.3 (continuous mapping):
If ξ_n → ξ in probability and f is measurable and a.s. continuous at ξ,
then f(ξ_n) → f(ξ) in probability. -/
lemma kallenberg_4_3
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Type*} [MetricSpace S] [MetricSpace T] [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
    (ξ : Ω → S) (ξ_seq : ℕ → Ω → S) (f : S → T)
    (hf : Measurable f) (hf_cont : ∀ᵐ ω ∂μ, ContinuousAt f (ξ ω))
    (hξ : Measurable ξ) (hξ_seq : ∀ n, Measurable (ξ_seq n))
    (h_prob : ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω) (ξ ω) > ε}) Filter.atTop (𝓝 0)) :
    ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (f (ξ_seq n ω)) (f (ξ ω)) > ε}) Filter.atTop (𝓝 0) := by
  sorry

/-- Lemma 4.4 (random sequences):
For separable metric spaces S₁, S₂, ..., let ξ = (ξ₁, ξ₂, ...) and ξⁿ = (ξ₁ⁿ, ξ₂ⁿ, ...) be random
elements in ×_k S_k. Then ξⁿ → ξ in probability iff ξ_kⁿ → ξ_k in probability for each k. -/
lemma kallenberg_4_4
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : Type*} [Encodable ι] (S : ι → Type*) [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, SecondCountableTopology (S i)]
    [MetricSpace ((i : ι) → S i)]
    (ξ : Ω → (∀ i, S i)) (ξ_seq : ℕ → Ω → (∀ i, S i))
    (hξ : Measurable ξ) (hξ_seq : ∀ n, Measurable (ξ_seq n)) :
    (∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω) (ξ ω) > ε}) Filter.atTop (𝓝 0)) ↔
    (∀ i, ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω i) (ξ ω i) > ε}) Filter.atTop (𝓝 0)) := by
  sorry

/-- Corollary 4.5 (elementary operations):
If ξ_n → ξ and η_n → η in probability, then aξ_n + bη_n → aξ + bη,
ξ_n η_n → ξ η, and ξ_n / η_n → ξ / η when η, η_n are a.s. nonzero. -/
lemma kallenberg_4_5
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ η : Ω → ℝ) (ξ_seq η_seq : ℕ → Ω → ℝ)
    (hξ : Measurable ξ) (hη : Measurable η) (hξ_seq : ∀ n, Measurable (ξ_seq n))
    (hη_seq : ∀ n, Measurable (η_seq n))
    (h_prob_ξ : ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | |ξ_seq n ω - ξ ω| > ε}) Filter.atTop (𝓝 0))
    (h_prob_η : ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | |η_seq n ω - η ω| > ε}) Filter.atTop (𝓝 0)) :
    (∀ ε > 0, Filter.Tendsto (fun n => μ {ω | |(ξ_seq n ω + η_seq n ω) - (ξ ω + η ω)| > ε}) Filter.atTop (𝓝 0)) ∧
    (∀ ε > 0, Filter.Tendsto (fun n => μ {ω | |(ξ_seq n ω * η_seq n ω) - (ξ ω * η ω)| > ε}) Filter.atTop (𝓝 0)) ∧
    ((∀ᵐ ω ∂μ, η ω ≠ 0) → (∀ᵐ ω ∂μ, ∀ n, η_seq n ω ≠ 0) →
      ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | |(ξ_seq n ω / η_seq n ω) - (ξ ω / η ω)| > ε}) Filter.atTop (𝓝 0)) := by
  sorry

/-- Lemma 4.6 (completeness):
For random elements in a complete metric space, (ξ_n) is Cauchy in probability
iff ξ_n → ξ in probability (or a.s. convergence respectively). -/
lemma kallenberg_4_6
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (ξ : Ω → S) (ξ_seq : ℕ → Ω → S)
    (hξ : Measurable ξ) (hξ_seq : ∀ n, Measurable (ξ_seq n))
    (h_complete : CompleteSpace S) :
    ((∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω) (ξ ω) > ε}) Filter.atTop (𝓝 0)) ↔
      (∃ ξ' : Ω → S, Measurable ξ' ∧
        ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω) (ξ' ω) > ε}) Filter.atTop (𝓝 0))) ∧
    ((∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω) (ξ ω) > ε}) Filter.atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂μ, Filter.Tendsto (fun n => ξ_seq n ω) Filter.atTop (𝓝 (ξ ω)))) := by
  sorry

/-- Lemma 4.7 (convergence in probability and in distribution):
ξ_n → ξ in probability implies ξ_n → ξ in distribution;
the two are equivalent when ξ is a.s. constant. -/
lemma kallenberg_4_7
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    (ξ : Ω → S) (ξ_seq : ℕ → Ω → S)
    (hξ : Measurable ξ) (hξ_seq : ∀ n, Measurable (ξ_seq n))
    (h_prob : ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | dist (ξ_seq n ω) (ξ ω) > ε}) Filter.atTop (𝓝 0)) :
    (∀ (f : S → ℝ), Measurable f → Continuous f →
      Filter.Tendsto (fun n => ∫ ω, f (ξ_seq n ω) ∂μ) Filter.atTop (𝓝 (∫ ω, f (ξ ω) ∂μ))) := by
  sorry

/-- Definition: (ξ_n) is tight if lim_{r→∞} sup_n P[|ξ_n| > r] = 0. -/
def Tight (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (ξ_seq : ℕ → Ω → (Fin d → ℝ)) : Prop :=
  Filter.Tendsto (fun r : ℝ => ⨆ n, μ {ω | ‖ξ_seq n ω‖ > r}) Filter.atTop (𝓝 0)

/-- Lemma 4.8 (weak convergence and tightness):
If ξ_n → ξ in distribution, then (ξ_n) is tight. -/
lemma kallenberg_4_8
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ξ : Ω → (Fin d → ℝ)) (ξ_seq : ℕ → Ω → (Fin d → ℝ))
    (hξ : Measurable ξ) (hξ_seq : ∀ n, Measurable (ξ_seq n))
    (h_dist : ∀ (f : (Fin d → ℝ) → ℝ), Measurable f → Continuous f →
      Filter.Tendsto (fun n => ∫ ω, f (ξ_seq n ω) ∂μ) Filter.atTop (𝓝 (∫ ω, f (ξ ω) ∂μ))) :
    Tight μ ξ_seq := by
  sorry

/-- Lemma 4.9 (tightness and convergence in probability):
(ξ_n) is tight iff c_n ξ_n → 0 in probability for any c_n → 0 with c_n ≥ 0. -/
lemma kallenberg_4_9
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ξ_seq : ℕ → Ω → (Fin d → ℝ))
    (hξ_seq : ∀ n, Measurable (ξ_seq n)) :
    Tight μ ξ_seq ↔
    (∀ (c : ℕ → ℝ), (∀ n, 0 ≤ c n) → Filter.Tendsto c Filter.atTop (𝓝 0) →
      ∀ ε > 0, Filter.Tendsto (fun n => μ {ω | ‖c n • ξ_seq n ω‖ > ε}) Filter.atTop (𝓝 0)) := by
  sorry

/-- Definition: (ξ_t) is uniformly integrable if
lim_{r→∞} sup_{t} E[|ξ_t|; |ξ_t| > r] = 0. -/
def UniformIntegrable (μ : Measure Ω) {T : Type*} (ξ : T → Ω → ℝ) : Prop :=
  Filter.Tendsto (fun r : ℝ => ⨆ t, ∫ ω in {ω | |ξ t ω| > r}, |ξ t ω| ∂μ) Filter.atTop (𝓝 0)

/-- Lemma 4.10 (uniform integrability):
A family of random variables (ξ_t) is uniformly integrable iff
sup_t E[|ξ_t|] < ∞ and lim_{P[A]→0} sup_{t} E[|ξ_t|; A] = 0. -/
lemma kallenberg_4_10
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Type*} (ξ : T → Ω → ℝ) (hξ : ∀ t, Measurable (ξ t))
    (h_bound : ∀ t, Integrable (ξ t) μ) :
    UniformIntegrable μ ξ ↔
    ((∃ C, ∀ t, ∫ ω, |ξ t ω| ∂μ ≤ C) ∧
      Filter.Tendsto (fun ε : ℝ => ⨆ t, ∫ ω in {ω | |ξ t ω| > ε}, |ξ t ω| ∂μ)
        Filter.atTop (𝓝 0)) := by
  sorry

/-- Lemma 4.11 (convergence of means):
For nonnegative random variables with ξ_n → ξ in distribution,
E[ξ] ≤ liminf E[ξ_n], and E[ξ_n] → E[ξ] < ∞ iff condition (5) holds
(uniform integrability). -/
lemma kallenberg_4_11
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → ℝ) (ξ_seq : ℕ → Ω → ℝ)
    (hξ_nonneg : ∀ ω, 0 ≤ ξ ω) (hξ_seq_nonneg : ∀ n ω, 0 ≤ ξ_seq n ω)
    (hξ_int : Integrable ξ μ) (hξ_seq_int : ∀ n, Integrable (ξ_seq n) μ)
    (hξ : Measurable ξ) (hξ_seq : ∀ n, Measurable (ξ_seq n))
    (h_dist : ∀ (f : ℝ → ℝ), Measurable f → Continuous f →
      Filter.Tendsto (fun n => ∫ ω, f (ξ_seq n ω) ∂μ) Filter.atTop (𝓝 (∫ ω, f (ξ ω) ∂μ))) :
    (∫ ω, ξ ω ∂μ ≤ Filter.liminf (fun n => ∫ ω, ξ_seq n ω ∂μ) Filter.atTop) ∧
    ((Filter.Tendsto (fun n => ∫ ω, ξ_seq n ω ∂μ) Filter.atTop (𝓝 (∫ ω, ξ ω ∂μ))) ↔
      Filter.Tendsto (fun r : ℝ => Filter.limsup (fun n => ∫ ω in {ω | |ξ_seq n ω| > r}, |ξ_seq n ω| ∂μ)
        Filter.atTop) Filter.atTop (𝓝 0)) := by
  sorry

end Chapter4
