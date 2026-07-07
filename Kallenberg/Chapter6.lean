import Mathlib

open Set MeasureTheory Filter Topology Function
open scoped MeasureTheory ProbabilityTheory ENNReal

namespace Chapter6

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The probability of a set under a probability measure, as a real number. -/
def prob (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : ℝ :=
  (μ s).toReal

/-! ### Conditional expectations and conditional distributions -/

/-- Theorem 6.1 (conditional expectation, Kolmogorov):
For any sub-σ-field F ⊂ A, there exists an a.s. unique linear operator
E^F : L^1 → L^1(F) satisfying the averaging property:
E[E^F ξ ; A] = E[ξ ; A] for all A ∈ F. -/
theorem kallenberg_6_1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) {F : MeasurableSpace Ω} (hm : F ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (ξ : Ω → E) (hξ : Integrable ξ μ) :
    AEStronglyMeasurable (fun ω => condExp F μ ξ ω) (μ.trim hm) ∧
    (∀ s, MeasurableSet s → μ s < ∞ →
      ∫ ω in s, condExp F μ ξ ω ∂μ = ∫ ω in s, ξ ω ∂μ) := by
  have h := condExp F μ ξ
  sorry

/-- Lemma 6.2 (local property):
If the σ-fields F, G and functions ξ, η satisfy F = G and ξ = η a.s. on A ∈ F ∩ G,
then condExp F μ ξ = condExp G μ η a.s. on A. -/
lemma kallenberg_6_2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) {F G : MeasurableSpace Ω} (hmF : F ≤ mΩ) (hmG : G ≤ mΩ)
    [SigmaFinite (μ.trim hmF)] [SigmaFinite (μ.trim hmG)]
    (ξ η : Ω → E) (hξ : Integrable ξ μ) (hη : Integrable η μ)
    (h_eq_fields : ∀ B, MeasurableSet[F] B ↔ MeasurableSet[G] B)
    (h_eq : ∀ᵐ ω ∂μ, ξ ω = η ω) :
    (fun ω => condExp F μ ξ ω) =ᵐ[μ.trim hmF] (fun ω => condExp G μ η ω) := by
  sorry

/-- Theorem 6.3 (conditional distribution):
For random elements ξ in a Borel space S and η in a measurable space T,
there exists a probability kernel κ from T to S satisfying
P[ξ ∈ B | η] = κ(η, B) a.s. for all B ∈ S, and κ is unique a.e. 𝒜(η). -/
theorem kallenberg_6_3
    {S T : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S] [SecondCountableTopology S]
    [MeasurableSpace T] [TopologicalSpace T] [SecondCountableTopology T] [BorelSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → S) (η : Ω → T) (hξ : Measurable ξ) (hη : Measurable η) :
    True := by
  sorry

/-- Lemma 6.4 (conditional probability):
The conditional probability P^F A = E[1_A | F] satisfies
E[P^F A ; B] = P(A ∩ B) for all B ∈ F. -/
lemma kallenberg_6_4
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hm : F ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (A : Set Ω) (hA : MeasurableSet A) :
    AEStronglyMeasurable (fun ω => condExp F μ (fun ω => (1 : ℝ)) ω) (μ.trim hm) := by
  sorry

/-- Lemma 6.5 (regular conditional distribution, existence):
For a random element ξ in a Borel space S, there exists an F-measurable
random probability measure P[ξ ∈ · | F] on S. -/
theorem kallenberg_6_5
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S] [SecondCountableTopology S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hm : F ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (ξ : Ω → S) (hξ : Measurable ξ) :
    True := by
  sorry

/-- Lemma 6.6 (regular conditional distribution, uniqueness):
If κ and κ' are two regular conditional distributions of ξ given F,
then κ = κ' a.e. on the set where F is defined. -/
theorem kallenberg_6_6
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hm : F ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (ξ : Ω → S) (hξ : Measurable ξ)
    (κ κ' : ProbabilityTheory.Kernel S S) (hκ : ProbabilityTheory.IsMarkovKernel κ) (hκ' : ProbabilityTheory.IsMarkovKernel κ')
    (hκ_eq : ∀ B, MeasurableSet B → (fun ω => κ (ξ ω) B) =ᵐ[μ.trim hm]
      (fun ω => κ' (ξ ω) B)) :
    True := by
  sorry

end Chapter6
