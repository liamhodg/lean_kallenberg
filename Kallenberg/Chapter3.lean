import Mathlib

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

namespace Chapter3

variable {Ω : Type*} [MeasurableSpace Ω]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The probability of a set under a probability measure, as a real number. -/
def prob (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : ℝ :=
  (μ s).toReal

/-- Lemma 3.1 (measurability): Fix a measurable space (S, 𝒮), an index set T,
and a subset U ⊆ S^T. Then X : Ω → U is measurable iff X_t : Ω → S is measurable for every t. -/
lemma kallenberg_3_1
    {S T : Type*} [MeasurableSpace S]
    (U : Set (T → S)) (X : Ω → T → S)
    (hX : ∀ ω, X ω ∈ U) :
    Measurable X ↔ ∀ t : T, Measurable (fun ω => X ω t) := by
  sorry

/-- Proposition 3.2 (finite-dimensional distributions): Two processes have the same
distribution iff all finite-dimensional distributions match. -/
lemma kallenberg_3_2
    {S T : Type*} [MeasurableSpace S]
    (U : Set (T → S)) (X Y : Ω → T → S)
    (hX : ∀ ω, X ω ∈ U) (hY : ∀ ω, Y ω ∈ U) :
    (MeasurableSpace.map X inferInstance = MeasurableSpace.map Y inferInstance) ↔
      (∀ (t : T) (B : Set S), MeasurableSet B →
        prob μ {ω | X ω t ∈ B} = prob μ {ω | Y ω t ∈ B}) := by
  sorry

/-- Lemma 3.3 (distribution functions): Two random vectors have the same distribution
iff their distribution functions are equal. -/
lemma kallenberg_3_3
    {d : ℕ} (ξ η : Ω → (Fin d → ℝ))
    (hξ : Measurable ξ) (hη : Measurable η) :
    (MeasurableSpace.map ξ inferInstance = MeasurableSpace.map η inferInstance) ↔
      (∀ x : Fin d → ℝ,
        prob μ {ω | ξ ω ≤ x} = prob μ {ω | η ω ≤ x}) := by
  sorry

/-- Lemma 3.4 (moments and tails): For ξ ≥ 0, E[ξ^p] = p ∫_0^∞ t^{p-1} P[ξ > t] dt. -/
lemma kallenberg_3_4
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (hξ_pos : ∀ ω, 0 < ξ ω)
    (hξ_int : Integrable ξ μ) {p : ℝ} (hp_pos : 0 < p) :
    ∫ ω, ξ ω ^ p ∂μ = p * ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * prob μ {ω | ξ ω > t} := by
  sorry

/-- Lemma 3.5 (convex maps, Jensen): For integrable ξ and convex f, E[f(ξ)] ≥ f(E[ξ]). -/
lemma kallenberg_3_5
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ξ : Ω → (Fin d → ℝ))
    (hξ : Measurable ξ) (hξ_int : Integrable ξ μ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    f (∫ ω, ξ ω ∂μ) ≤ ∫ ω, f (ξ ω) ∂μ := by
  sorry

/-- Lemma 3.6 (extension): Independence of π-systems extends to generated σ-fields. -/
lemma kallenberg_3_6
    {T : Type*} (C F : T → Set (Set Ω))
    (hCF : ∀ t, C t ⊆ F t)
    (h_indep : ∀ (J : Finset T), J.Nonempty →
      ∀ (A : T → Set Ω), (∀ t ∈ J, A t ∈ C t) →
      prob μ (⋂ t ∈ J, A t) = ∏ t ∈ J, prob μ (A t)) :
    ∀ (J : Finset T), J.Nonempty →
      ∀ (A : T → Set Ω), (∀ t ∈ J, A t ∈ F t) →
      prob μ (⋂ t ∈ J, A t) = ∏ t ∈ J, prob μ (A t) := by
  sorry

/-- Corollary 3.7 (grouping): Independence extends to generated σ-fields of disjoint partitions. -/
lemma kallenberg_3_7
    {T : Type*} (𝒯 : Set (Set T))
    (F : T → Set (Set Ω))
    (h_indep : ∀ (J : Finset T), J.Nonempty →
      ∀ (A : T → Set Ω), (∀ t ∈ J, A t ∈ F t) →
      prob μ (⋂ t ∈ J, A t) = ∏ t ∈ J, prob μ (A t))
    (h_partition : ∀ S ∈ 𝒯, ∀ t ∈ S, ∀ U ∈ 𝒯, U ≠ S → t ∉ U)
    (h_cover : ⋃ S ∈ 𝒯, S = Set.univ) :
    ∀ (J : Finset (Set T)), J.Nonempty →
      (∀ S ∈ J, S ∈ 𝒯) →
      ∀ (A : (Set T) → Set Ω), (∀ S ∈ J, A S ∈ F S) →
      prob μ (⋂ S ∈ J, A S) = ∏ S ∈ J, prob μ (A S) := by
  sorry

/-- Lemma 3.8 (pairwise independence): Full independence is equivalent to pairwise
independence for a separating class. -/
lemma kallenberg_3_8
    {T : Type*} (𝒯 : Set (Set T))
    (F : T → Set (Set Ω))
    (h_sep : ∀ (s t : T), s ≠ t → ∃ S ∈ 𝒯, (s ∈ S ∧ t ∉ S) ∨ (t ∈ S ∧ s ∉ S)) :
    ((∀ (J : Finset T), J.Nonempty →
      ∀ (A : T → Set Ω), (∀ t ∈ J, A t ∈ F t) →
      prob μ (⋂ t ∈ J, A t) = ∏ t ∈ J, prob μ (A t)) ↔
      (∀ (S : Set T), S ∈ 𝒯 →
        ∀ (A : T → Set Ω), (∀ t ∈ S, A t ∈ F t) → (∀ t ∉ S, A t ∈ F t) →
        prob μ (⋂ t, A t) = prob μ (⋂ t ∈ S, A t) * prob μ (⋂ t ∉ S, A t))) := by
  sorry

/-- Lemma 3.9 (triviality and degeneracy): A P-trivial σ-field satisfies F ⟂ F,
and any F-measurable random element is a.s. degenerate. -/
lemma kallenberg_3_9
    (F : Set (Set Ω))
    (h_trivial : ∀ A ∈ F, prob μ A = 0 ∨ prob μ A = 1) :
    (∀ A ∈ F, ∀ B ∈ F, prob μ (A ∩ B) = prob μ A * prob μ B) := by
  sorry

/-- Lemma 3.10 (product measures): Random elements are independent iff their joint
distribution equals the product of their marginals. -/
lemma kallenberg_3_10
    {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ k, Measurable (ξ k)) :
    ((∀ (J : Finset (Fin n)), J.Nonempty →
      ∀ (A : Fin n → Set ℝ), (∀ k ∈ J, MeasurableSet (A k)) →
      prob μ (⋂ k ∈ J, {ω | ξ k ω ∈ A k}) = ∏ k ∈ J, prob μ {ω | ξ k ω ∈ A k}) ↔
      (∀ (A : Fin n → Set ℝ), (∀ k, MeasurableSet (A k)) →
        prob μ (⋂ k, {ω | ξ k ω ∈ A k}) = ∏ k, prob μ {ω | ξ k ω ∈ A k})) := by
  sorry

/-- Lemma 3.11 (conditioning): For independent ξ, η and measurable f,
E[f(ξ, η)] = E[E[f(ξ, η')]_{η'}]_{ξ}. -/
lemma kallenberg_3_11
    {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ξ : Ω → S) (η : Ω → T) (f : S → T → ℝ)
    (hξ : Measurable ξ) (hη : Measurable η) (hf : Measurable (fun (p : S × T) => f p.1 p.2))
    (h_int : Integrable (fun ω => f (ξ ω) (η ω)) μ) :
    ∫ ω, f (ξ ω) (η ω) ∂μ = ∫ ω, (∫ ω', f (ξ ω) (η ω') ∂μ) ∂μ := by
  sorry

/-- Corollary 3.12 (convolution): The product of independent random elements has
distribution equal to the convolution of their distributions. -/
lemma kallenberg_3_12
    {G : Type*} [MeasurableSpace G] [MeasurableMul G]
    (ξ η : Ω → G)
    (hξ : Measurable ξ) (hη : Measurable η) :
    (MeasurableSpace.map (fun ω => ξ ω * η ω) inferInstance =
      MeasurableSpace.map (fun (x, y) : G × G => x * y) (by infer_instance)) := by
  sorry

/-- Theorem 3.13 (Kolmogorov's 0-1 law): The tail σ-field of independent σ-fields is P-trivial. -/
lemma kallenberg_3_13
    (F : ℕ → Set (Set Ω))
    (h_indep : ∀ (J : Finset ℕ), J.Nonempty →
      ∀ (A : ℕ → Set Ω), (∀ n ∈ J, A n ∈ F n) →
      prob μ (⋂ n ∈ J, A n) = ∏ n ∈ J, prob μ (A n)) :
    (prob μ (⋂ n, ⋃ k > n, Set.univ) = 0) ∨
    (prob μ (⋂ n, ⋃ k > n, Set.univ) = 1) := by
  sorry

/-- Theorem 3.18 (Borel-Cantelli): ∑ P A_n < ∞ implies P(A_n i.o.) = 0. -/
lemma kallenberg_3_18
    (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet (A n)) :
    (∑' n, prob μ (A n) < ∞) → (prob μ {ω | ∀ N, ∃ n ≥ N, ω ∈ A n} = 0) := by
  sorry

end Chapter3
