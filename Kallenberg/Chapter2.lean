import Mathlib
open ENNReal
open Set MeasureTheory Filter Topology Function


variable {Ω : Type*}

namespace MeasureTheory

/-- `IsCaratheodory m s` says the set `s` is Carathéodory measurable with respect to the outer
    measure `m`: for all E ⊆ Ω, m(E) = m(E ∩ s) + m(E \ s). -/
def IsCaratheodory (m : OuterMeasure Ω) (s : Set Ω) : Prop :=
  ∀ t, m t = m (t ∩ s) + m (t \ s)

end MeasureTheory

namespace Chapter2

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Outer measures and Carathéodory's theorem -/

/-- Theorem 2.1 (restriction of outer measure, Carathéodory):
    Let m be an outer measure on Ω, and write 𝒜 for the class of m-measurable sets.
    Then 𝒜 is a σ-field and the restriction of m to 𝒜 is a measure. -/
theorem kallenberg_2_1 (m : OuterMeasure Ω) :
    True := by
  sorry

/-! ### Lebesgue measure -/

/-- Theorem 2.2 (Lebesgue measure, Borel):
    There exists a unique measure on (ℝ, ℬ) such that μ(I) = |I| for every interval I ⊆ ℝ. -/
theorem kallenberg_2_2 :
    ∃! μ : Measure ℝ, IsProbabilityMeasure (μ.restrict (Set.Icc (-1 : ℝ) 1)) := by
  sorry

/-- Lemma 2.3 (outer Lebesgue measure):
    The function λ* defined by λ*(A) = inf { Σ |I_n| : A ⊆ ⋃_n I_n, I_n open intervals }
    is an outer measure on ℝ, and λ*(I) = |I| for every interval I. -/
lemma kallenberg_2_3 :
    ∃ m : OuterMeasure ℝ, (∀ I : Set ℝ, Set.OrdConnected I → m I = volume I) := by
  sorry

/-- Lemma 2.4 (measurability of intervals):
    The interval (-∞, a] is λ*-measurable for every a ∈ ℝ. -/
lemma kallenberg_2_4 (a : ℝ) :
    (Classical.choose (kallenberg_2_3)).IsCaratheodory (Set.Iic a) := by
  sorry

/-! ### Extension and product measures -/

/-- Theorem 2.5 (extension, Carathéodory):
    Let μ be a finitely additive and countably subadditive set function on a semiring 𝒯
    such that μ(∅) = 0. Then μ extends to a measure on σ(𝒯). -/
theorem kallenberg_2_5 {𝒯 : Set (Set Ω)} (h_semiring : IsSetSemiring 𝒯)
    (μ : Set Ω → ENNReal)
    (h_add : ∀ s ∈ 𝒯, ∀ t ∈ 𝒯, s ∩ t = ∅ → μ (s ∪ t) = μ s + μ t)
    (h_countable_subadd :
      ∀ f : ℕ → Set Ω, (∀ n, f n ∈ 𝒯) → μ (⋃ n, f n) ≤ ∑' n, μ (f n))
    (h_empty : μ ∅ = 0) :
    ∃ ν : Measure Ω, (∀ s ∈ 𝒯, ν s = μ s) ∧
      (∀ s, MeasurableSet s → ν s = μ s) := by
  sorry

/-- Theorem 2.6 (invariance of Lebesgue measure):
    Fix any measurable space (S, 𝒮) and a measure μ on ℝ^d × S with σ-finite projection
    ν = μ((0,1)^d × ·) onto S. Then μ is invariant under shifts in ℝ^d iff μ = λ ⊗ ν,
    in which case μ remains invariant under arbitrary rigid motions of ℝ^d. -/
theorem kallenberg_2_6 {d : ℕ} (S : Type*) [MeasurableSpace S]
    (μ : Measure ((Fin d → ℝ) × S))
    (h_proj : SigmaFinite (Measure.map Prod.snd μ)) :
    (∀ h : Fin d → ℝ, Measure.map (fun (x, s) => (x + h, s)) μ = μ) ↔
    μ = (volume : Measure (Fin d → ℝ)).prod (Measure.map Prod.snd μ) := by
  sorry

/-! ### Mean continuity and signed measures -/

/-- Lemma 2.7 (mean continuity):
    Let f be a measurable function on ℝ^d with ∫ |f| < ∞. Then
    lim_{h→0} ∫ |f(x+h) - f(x)| dx = 0. -/
lemma kallenberg_2_7 {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (hf_int : Integrable f volume) :
    Filter.Tendsto (fun h : Fin d → ℝ => ∫ x : Fin d → ℝ, |f (x + h) - f x|)
      (nhds 0) (nhds 0) := by
  sorry

/-- Theorem 2.8 (Hahn decomposition):
    Any bounded signed measure can be written uniquely as a difference of two bounded,
    nonnegative, and mutually singular measures. -/
theorem kallenberg_2_8 {ν : VectorMeasure Ω ℝ} :
    ∃! p : Measure Ω × Measure Ω, (IsFiniteMeasure p.1) ∧ (IsFiniteMeasure p.2) ∧
    (∃ s, MeasurableSet s ∧ p.1 s = 0 ∧ p.2 sᶜ = 0) ∧
    (∀ s, MeasurableSet s →
      (ν s : ℝ) = (ENNReal.toReal (p.1 s)) - (ENNReal.toReal (p.2 s))) := by
  sorry

/-- Corollary 2.9 (maximum and minimum of measures):
    For any σ-finite measures μ and ν on a common measurable space, there exists a largest
    measure bounded by μ and ν and a smallest measure bounding μ and ν. -/
lemma kallenberg_2_9 {μ ν : Measure Ω} (hμ : SigmaFinite μ) (hν : SigmaFinite ν) :
    (∃ ξ : Measure Ω, (ξ ≤ μ) ∧ (ξ ≤ ν) ∧
      (∀ ζ, ζ ≤ μ → ζ ≤ ν → ζ ≤ ξ)) ∧
    (∃ ζ : Measure Ω, (μ ≤ ζ) ∧ (ν ≤ ζ) ∧
      (∀ ξ, μ ≤ ξ → ν ≤ ξ → ζ ≤ ξ)) := by
  sorry

/-- Theorem 2.10 (Lebesgue decomposition, Radon-Nikodym):
    For any σ-finite measures μ and ν on (Ω, 𝒜), there exist unique measures ν_a and ν_s
    such that ν = ν_a + ν_s, where ν_a ≪ μ and ν_s is mutually singular with μ. -/
theorem kallenberg_2_10 {μ ν : Measure Ω} (hμ : SigmaFinite μ) (hν : SigmaFinite ν) :
    ∃! p : Measure Ω × Measure Ω,
      (p.1 ≪ μ) ∧ (p.2.MutuallySingular μ) ∧ ν = p.1 + p.2 := by
  sorry

/-- Lemma 2.11 (closure):
    For two measures μ and ν on Ω and some measurable functions f_n, g_n ≥ 0 on Ω
    with f_n ↑ μ-a.e. and g_n ↑ ν-a.e., then sup_n f_n · g_n < ν, where f = sup_n f_n
    and g = sup_n g_n. -/
lemma kallenberg_2_11 {μ ν : Measure Ω} (f g : ℕ → Ω → ℝ)
    (hf_nonneg : ∀ n x, 0 ≤ f n x)
    (hg_nonneg : ∀ n x, 0 ≤ g n x)
    (hf_mono : ∀ x, Monotone (fun n => f n x))
    (hg_mono : ∀ x, Monotone (fun n => g n x))
    (hf_lim : ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (sSup (range (fun n => f n x)))))
    (hg_lim : ∀ᵐ x ∂ν,
      Filter.Tendsto (fun n => g n x) Filter.atTop (nhds (sSup (range (fun n => g n x))))) :
    ν ≪ μ := by
  sorry

/-- Lemma 2.12 (partial density):
    Let μ and ν be finite measures on Ω with μ ≠ ν. Then there exists a measurable
    function f > 0 such that ∫ f dμ > 0 and f · μ ≤ ν. -/
lemma kallenberg_2_12 {μ ν : Measure Ω} (hμ : IsFiniteMeasure μ) (hν : IsFiniteMeasure ν)
    (h_ne : μ ≠ ν) :
    ∃ f : Ω → ℝ, Measurable f ∧ (∀ x, 0 < f x) ∧ (∫ x, f x ∂μ > 0) ∧
      (∀ s, MeasurableSet s → ENNReal.ofReal (∫ x in s, f x ∂μ) ≤ ν s) := by
  sorry

/-- Corollary 2.13 (splitting):
    Consider two finite measure spaces (S, 𝒮, μ) and (T, 𝒯, ν) and a measurable map
    f: S → T such that ν ≪ μ ∘ f⁻¹. Then there exists a measure μ! ≪ μ on S
    such that ν = μ! ∘ f⁻¹. -/
lemma kallenberg_2_13 {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) (f : S → T) (hf : Measurable f)
    (h_abs : ν ≪ Measure.map f μ) :
    ∃ μ' : Measure S, μ' ≪ μ ∧ Measure.map f μ' = ν := by
  sorry

/-! ### Lebesgue-Stieltjes measures -/

/-- Proposition 2.14 (Lebesgue-Stieltjes measures):
    The relation μ(a, b] = F(b) - F(a) defines a one-to-one correspondence between
    locally finite measures on ℝ and right-continuous, nondecreasing functions F on ℝ
    with F(-∞) = 0. -/
lemma kallenberg_2_14 (F : ℝ → ℝ) (hF_nondec : Monotone F)
    (hF_rightcont : ∀ x, Filter.Tendsto F (𝓝[>] x) (𝓝 (F x)))
    (hF_neg_inf : Filter.Tendsto F Filter.atBot (𝓝 0)) :
    ∃! μ : Measure ℝ, IsFiniteMeasureOnCompacts μ ∧
      ∀ a b, a < b → μ (Set.Ioc a b) = ENNReal.ofReal (F b - F a) := by
  sorry

/-! ### Differentiation -/

/-- Theorem 2.15 (differentiation, Lebesgue):
    Any nondecreasing and right-continuous function F can be written as F = f + F_s
    where f is absolutely continuous and F_s is singular. Then F is differentiable a.e.
    with derivative f. -/
theorem kallenberg_2_15 (F : ℝ → ℝ) (hF_nondec : Monotone F)
    (hF_rightcont : ∀ x, Filter.Tendsto F (𝓝[>] x) (𝓝 (F x))) :
    ∃ (f F_s : ℝ → ℝ), (∀ x, F x = (∫ t in Set.Iic x, f t) + F_s x) ∧
      (∀ᵐ x ∂(volume.restrict Set.univ), HasDerivAt F (f x) x) := by
  sorry

/-- Lemma 2.16 (interval selection):
    Let 𝒯 be a class of open intervals with union G. If |G| < ∞, there exist some disjoint
    sets I_1, ..., I_n ∈ 𝒯 with Σ |I_k| > |G|/4. -/
lemma kallenberg_2_16 {𝒯 : Set (Set ℝ)} (h_open : ∀ I ∈ 𝒯, IsOpen I)
    (h_interval : ∀ I ∈ 𝒯, ∃ a b, I = Set.Ioo a b)
    (G : Set ℝ) (h_union : G = Set.sUnion 𝒯) (hG_finite : volume G < (⊤ : ENNReal)) :
    ∃ I : ℕ → Set ℝ, (∀ n, I n ∈ 𝒯) ∧ (Pairwise (onFun Disjoint I)) ∧
      (∑' n, volume (I n)) > volume G / 4 := by
  sorry

/-- Lemma 2.17 (differentiation on null sets):
    Let F(x) = ν(0, x] for some locally finite measure ν on ℝ, and let A ∈ 𝒩 with ν(A) = 0.
    Then F' = 0 a.e. on A. -/
lemma kallenberg_2_17 {ν : Measure ℝ} (hν : IsFiniteMeasureOnCompacts ν)
    (A : Set ℝ) (hA : MeasurableSet A) (hνA : ν A = 0) :
    ∀ᵐ x ∂(volume.restrict A),
      HasDerivAt ((fun (y : ℝ) => (ν (Set.Ioc 0 y)).toReal) : ℝ → ℝ) (0 : ℝ) x := by
  sorry

/-! ### Functions of finite variation -/

/-- Proposition 2.18 (Jordan decomposition):
    A function F on ℝ has locally finite variation iff it is a difference of two nondecreasing
    functions F_+ and F_-. -/
lemma kallenberg_2_18 (F : ℝ → ℝ) :
    (∃ (Fp Fm : ℝ → ℝ), (Monotone Fp) ∧ (Monotone Fm) ∧ (∀ x, F x = Fp x - Fm x)) := by
  sorry

/-- Proposition 2.19 (left and right continuity):
    Any function F of locally finite variation can be written as F = F_r + F_l where
    F_r is right-continuous with left-hand limits and F_l is left-continuous with right-hand limits. -/
lemma kallenberg_2_19 (F : ℝ → ℝ) :
    ∃ (F_r F_l : ℝ → ℝ), (∀ x, Filter.Tendsto F (𝓝[≥] x) (𝓝 (F_r x))) ∧
    (∀ x, Filter.Tendsto F (𝓝[≤] x) (𝓝 (F_l x))) ∧
    (∀ x, F x = F_r x + F_l x) := by
  sorry

/-- Proposition 2.20 (finite-variation functions and signed measures):
    For any right-continuous function F of locally finite variation, there exists a unique
    signed measure ν on ℝ such that ν(s, t] = F(t) - F(s) for all s < t. -/
lemma kallenberg_2_20 (F : ℝ → ℝ)
    (hF_rightcont : ∀ x, Filter.Tendsto F (𝓝[>] x) (𝓝 (F x))) :
    True := by
  sorry

/-- Proposition 2.21 (absolutely continuous and singular functions):
    Let F be a right-continuous function on ℝ of locally finite variation, and let ν
    be the associated signed measure on ℝ with ν(s, t] = F(t) - F(s). Then F is absolutely
    continuous or singular iff the corresponding property holds for ν. -/
lemma kallenberg_2_21 {F : ℝ → ℝ} (hF_nondec : Monotone F)
    (hF_rightcont : ∀ x, Filter.Tendsto F (𝓝[>] x) (𝓝 (F x)))
    (ν : VectorMeasure ℝ ℝ)
    (hν : ∀ s t, s < t → (ν (Set.Ioc s t) : ℝ) = F t - F s) :
    ((∀ ε > 0, ∃ δ > 0, ∀ (s : ℕ → ℝ) (t : ℕ → ℝ),
      (Pairwise (onFun Disjoint (fun n => Set.Ioo (s n) (t n)))) →
      (∑' n, ENNReal.ofReal (t n - s n)) < ENNReal.ofReal δ →
      (∑' n, ENNReal.ofReal |F (t n) - F (s n)|) < ENNReal.ofReal ε) ↔
    (∀ s, MeasurableSet s → volume s = 0 → ν s = 0)) := by
  sorry

/-! ### Riesz representation -/

/-- Theorem 2.22 (Riesz representation):
    If S is locally compact, second countable, and Hausdorff (lscH), then every positive
    linear functional on C_c(S) extends uniquely to a Radon measure on S. -/
theorem kallenberg_2_22 {S : Type*} [TopologicalSpace S] [SecondCountableTopology S]
    [T2Space S] [LocallyCompactSpace S] [MeasurableSpace S] [BorelSpace S]
    (Λ : (CompactlySupportedContinuousMap S ℝ) → ℝ) (h_add : ∀ f g, Λ (f + g) = Λ f + Λ g)
    (h_nonneg : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ Λ f)
    (h_hom : ∀ (c : ℝ) f, Λ (c • f) = c * Λ f) :
    ∃! μ : Measure S, IsFiniteMeasureOnCompacts μ ∧ ∀ f, Λ f = ∫ x, f x ∂μ := by
  sorry

/-- Lemma 2.23 (partition of unity):
    For any open cover G_1, ..., G_n of a compact set K ⊆ S, there exist functions
    f_1, ..., f_n ∈ C_c(S) with f_k < G_k such that Σ f_k = 1 on K. -/
lemma kallenberg_2_23 {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (K : Set S) (hK : IsCompact K) (G : ℕ → Set S) (hG_open : ∀ n, IsOpen (G n))
    (h_cover : K ⊆ ⋃ n, G n) :
    ∃ (N : ℕ) (f : Fin N → CompactlySupportedContinuousMap S ℝ),
    (∀ k, {x | (f k : S → ℝ) x ≠ 0} ⊆ G k) ∧ (∀ x ∈ K, (∑ k, f k x) = 1) := by
  sorry

/-- Lemma 2.24 (inner approximation):
    For any positive linear functional Λ on C_c(S), define an inner content ν on S by
    ν(G) = sup { Λ(f) : f < G } for G ∈ G. Then ν is an inner content. -/
lemma kallenberg_2_24 {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] (Λ : (CompactlySupportedContinuousMap S ℝ) → ℝ) (hΛ_nonneg : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ Λ f) :
    True := by
  sorry

/-- Lemma 2.25 (outer approximation):
    Every inner content ν on S admits an extension to a regular outer measure. -/
lemma kallenberg_2_25 {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (ν : Set S → ENNReal) (hν_nondec : ∀ A B, A ⊆ B → ν A ≤ ν B)
    (hν_finite : ∀ G, IsOpen G → ν G < ∞)
    (hν_inner_cont : ∀ G, IsOpen G → ν G = sSup (ν '' {K | IsCompact K ∧ K ⊆ G}))
    (hν_add : ∀ K₁ K₂, Disjoint K₁ K₂ → IsCompact K₁ → IsCompact K₂ → ν (K₁ ∪ K₂) = ν K₁ + ν K₂)
    (hν_countable_subadd : ∀ K : ℕ → Set S, (∀ n, IsCompact (K n)) → IsCompact (⋃ n, K n) → ν (⋃ n, K n) ≤ ∑' n, ν (K n)) :
    ∃ μ : OuterMeasure S, (∀ G, IsOpen G → μ G = ν G) ∧
    (∀ A, μ A = sInf (μ '' {G | IsOpen G ∧ A ⊆ G})) ∧
    (∀ A, μ A = sSup (μ '' {K | IsCompact K ∧ K ⊆ A})) := by
  sorry

/-- Lemma 2.26 (measurability):
    If μ is a regular outer measure on S, then every Borel set in S is μ-measurable. -/
lemma kallenberg_2_26 {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : OuterMeasure S) (hμ_regular : ∀ G, IsOpen G → μ G = sInf (μ '' {G' | IsOpen G' ∧ G ⊆ G'}))
    (hμ_inner_regular : ∀ A, μ A = sSup (μ '' {K | IsCompact K ∧ K ⊆ A})) :
    ∀ s, @MeasurableSet S _ s := by
  sorry

/-! ### Haar and invariant measures -/

/-- Theorem 2.27 (Haar measure):
    On every lscH group G there exists, uniquely up to a normalization, a left-invariant
    Radon measure ≠ 0. If G is compact, then the measure is also right-invariant. -/
theorem kallenberg_2_27 {G : Type*} [TopologicalSpace G] [Group G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] :
    ∃! μ : Measure G, IsFiniteMeasureOnCompacts μ ∧ μ ≠ 0 ∧
    (∀ g : G, Measure.map (fun x => g * x) μ = μ) := by
  sorry

/-- Lemma 2.28 (near superadditivity):
    For any f, f' ∈ C_c(G) and ε > 0, there exists an open set U ≠ ∅ such that
    A_{f+f'} ≤ A_f + A_{f'} + ε on U, where A_f = inf { Σ c_i : f ≤ Σ c_i · 1_{x_i} }. -/
lemma kallenberg_2_28 {G : Type*} [TopologicalSpace G] [Group G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f f' : CompactlySupportedContinuousMap G ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set G, IsOpen U ∧ U.Nonempty ∧
    (∀ x ∈ U, (∫ x, (f + f') x ∂μ) ≤
      (∫ x, f x ∂μ) + (∫ x, f' x ∂μ) + ε) := by
  sorry

/-- Theorem 2.29 (invariant measure):
    Consider an lscH group G that acts transitively and properly on an lscH space S.
    Then there exists, uniquely up to a normalization, a G-invariant Radon measure ≠ 0 on S. -/
theorem kallenberg_2_29 {G S : Type*} [TopologicalSpace G] [Group G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S] [T2Space S]
    [SecondCountableTopology S] [MulAction G S] [ProperSMul G S]
    (h_trans : Function.Surjective (fun (g : G) (s : S) => g • s)) :
    ∃! μ : Measure S, IsFiniteMeasureOnCompacts μ ∧ μ ≠ 0 ∧
    (∀ g : G, ∀ B : Set S, MeasurableSet B → μ ((fun s => g • s) '' B) = μ B) := by
  sorry

end Chapter2
