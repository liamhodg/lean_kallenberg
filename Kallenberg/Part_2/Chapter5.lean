import Mathlib

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

variable {β : Type*} [MeasurableSpace β]

def IsRandomVariable (ξ : Ω → β) : Prop :=
  Measurable ξ

def IsNonNegRandomVariable (ξ : Ω → ℝ) : Prop :=
  IsRandomVariable ξ ∧ 0 ≤ ξ

end ProbabilityTheory

open ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

def prob (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : ℝ :=
  (μ s).toReal

lemma indicator_mul_le
  {ξ : Ω → ℝ} (hξ_nonneg : ∀ ω, 0 ≤ ξ ω) {a : ℝ} :
  ∀ ω, a * Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω ≤ ξ ω := by
  classical
  intro ω
  by_cases hω : ξ ω ≥ a
  · have h_le : a ≤ ξ ω := hω
    have h_indicator :
        Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω = (1 : ℝ) := by
      simp [Set.mem_setOf_eq, hω]
    have :
        a *
            Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω = a :=
      by
      simp [h_indicator]
    simpa [this]
      using h_le
  · have hξω : 0 ≤ ξ ω := hξ_nonneg ω
    have h_indicator :
        Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω = (0 : ℝ) :=
      by
      simp [Set.mem_setOf_eq, hω]
    have :
        a *
            Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω = 0 :=
      by
      simp [h_indicator]
    simp [this, hξω]

lemma measurable_indicator_mul_const {ξ : Ω → ℝ}
  (hξ_meas : Measurable ξ) {a : ℝ} :
  Measurable fun ω : Ω =>
    a * Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  have hs : MeasurableSet {ω : Ω | ξ ω ≥ a} := by
    have : {ω : Ω | ξ ω ≥ a} = ξ ⁻¹' Set.Ici a := by
      ext ω; simp [Set.mem_setOf_eq, Set.mem_Ici, ge_iff_le]
    simpa [this] using hξ_meas measurableSet_Ici
  have h_indicator : Measurable fun ω : Ω =>
      Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω :=
    (measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator hs
  exact (measurable_const.mul h_indicator)

lemma integrable_indicator_mul_const {ξ : Ω → ℝ}
  (hξ_meas : Measurable ξ) {a : ℝ}
  (μ : Measure Ω) [IsProbabilityMeasure μ] :
  Integrable (fun ω : Ω =>
    a * Set.indicator {ω | ξ ω ≥ a} (fun _ : Ω => (1 : ℝ)) ω) μ := by
  classical
  set s := {ω : Ω | ξ ω ≥ a}
  have hs : MeasurableSet s := by
    have : s = ξ ⁻¹' Set.Ici a := by
      ext ω; simp [s, Set.mem_setOf_eq, Set.mem_Ici, ge_iff_le]
    simpa [this] using hξ_meas measurableSet_Ici
  have h_const : Integrable (fun _ : Ω => a) μ := by
    simp [integrable_const (μ := μ) (c := a)]
  have h_indicator : Integrable (fun ω : Ω => Set.indicator s (fun _ : Ω => a) ω) μ :=
    h_const.indicator hs
  have h_eq :
      (fun ω : Ω => a * Set.indicator s (fun _ : Ω => (1 : ℝ)) ω) =
        fun ω : Ω => Set.indicator s (fun _ : Ω => a) ω := by
    funext ω
    by_cases hω : ω ∈ s
    · simp [hω, s]
    · simp [hω, s]
  simpa [s, h_eq]
    using h_indicator

lemma real_markov
  (μ : Measure Ω) [IsProbabilityMeasure μ] {ξ : Ω → ℝ}
  (hξ_meas : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω) (hξ_int : Integrable ξ μ)
  {a : ℝ} :
  prob μ {ω | ξ ω ≥ a} * a ≤ μ[ξ] := by
  set s : Set Ω := {ω | ξ ω ≥ a}
  have hs : MeasurableSet s := by
    have : s = ξ ⁻¹' Set.Ici a := by
      ext ω; simp [s, Set.mem_setOf_eq, Set.mem_Ici, ge_iff_le]
    simpa [this] using hξ_meas measurableSet_Ici
  let g : Ω → ℝ := fun ω => a * Set.indicator s (fun _ : Ω => (1 : ℝ)) ω
  have hg_le : g ≤ fun ω => ξ ω := indicator_mul_le hξ_nonneg
  have hg_integrable : Integrable g μ :=
    integrable_indicator_mul_const (μ := μ) hξ_meas (a := a)
  have h_le_integral : ∫ ω, g ω ∂μ ≤ μ[ξ] := by
    have h_le' : g ≤ᵐ[μ] fun ω => ξ ω := ae_of_all μ hg_le
    simpa [g] using integral_mono_ae hg_integrable hξ_int h_le'
  have hg_eq_indicator : g = Set.indicator s (fun _ : Ω => a) := by
    funext ω
    by_cases hω : ω ∈ s
    · simp [g, s, hω]
    · simp [g, s, hω]
  have h_integral_g : ∫ ω, g ω ∂μ = μ.real s * a := by
    have := integral_indicator_const (μ := μ) (s := s) (e := a) hs
    simpa [g, hg_eq_indicator, smul_eq_mul, mul_comm] using this
  have h_integral_le' : μ.real s * a ≤ μ[ξ] := by
    simpa [h_integral_g]
      using h_le_integral
  simpa [prob, Measure.real, s, mul_comm, mul_left_comm, mul_assoc]
      using h_integral_le'

/-- Lemma 5.1(a) (moments and tails, Chebyshev)
For any random variable ξ ≥ 0 with 0 < 𝔼[ξ] < ∞, we have
ℙ(ξ > r 𝔼[ξ]) ≤ 1/r.
-/
lemma kallenberg_5_1_a
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ξ : Ω → ℝ} (hξ : IsNonNegRandomVariable ξ) (hξ_int : Integrable ξ μ)
  (hξ_pos : 0 < μ[ξ]) {r : ℝ} (hr_pos : 0 < r) :
  prob μ {ω | ξ ω > r * μ[ξ]} ≤ 1 / r := by
  sorry


lemma paley_zygmund_precursor
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ξ : Ω → ℝ} (hξ : IsNonNegRandomVariable ξ)
  (hξ_int : Integrable ξ μ) (hξ_sq_int : Integrable (fun ω => (ξ ω) ^ 2) μ)
  (hξ_pos : 0 < μ[ξ]) {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) {t : ℝ}
  (ht_pos : 0 < t) :
  t ^ 2 * prob μ {ω | ξ ω > r} ≥
      2 * t * (1 - r) - moment ξ 2 μ
     := by
    sorry


/-- Lemma 5.1(b) (moments and tails, Bienayme, Paley & Zygmund)
For any random variable ξ ≥ 0 with 0 < 𝔼[ξ] < ∞ and 0 < r < 1,
we have ℙ(ξ > r 𝔼[ξ]) ≥ (1 - r)² (𝔼[ξ])² / (𝔼[ξ²]).
-/
lemma kallenberg_5_1_b
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ξ : Ω → ℝ} (hξ : IsNonNegRandomVariable ξ)
  (hξ_int : Integrable ξ μ) (hξ_sq_int : Integrable (fun ω => (ξ ω) ^ 2) μ)
  (hξ_pos : 0 < μ[ξ]) {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) :
  ((1 - r) ^ 2 * (μ[ξ]) ^ 2) / moment ξ 2 μ ≤
    prob μ {ω | ξ ω > r * μ[ξ]} := by
  sorry

/-- Lemma 5.1(c) (moments and tails, Chebyshev)
For any square-integrable random variable ξ, we have
ℙ(|ξ - 𝔼[ξ]| > r) ≤ Var(ξ) / r².
-/
lemma kallenberg_5_1_c
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {ξ : Ω → ℝ} (hξ : IsRandomVariable ξ) (hξ_int2 : Integrable (fun ω => ξ ω ^ 2) μ)
  {r : ℝ} (hr_pos : 0 < r) :
  prob μ {ω | |ξ ω - μ[ξ]| > r} ≤ variance ξ μ / (r ^ 2) := by
  sorry
