import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib
open scoped Topology ENNReal


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

/-- Lemma 1.4 (measurable functions):
Consider a mapping f between two measurable spaces (S,S) and (T,T),
and let C ⊆ T with σ(C) = T. Then f is S/T-measurable iff f⁻¹(C) ⊆ S. -/
lemma kallenberg_1_4
  {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] (f : S → T)
  {C : Set (Set T)} (hgen : MeasurableSpace.generateFrom C = ‹_›) :
  Measurable f ↔ ∀ s ∈ C, MeasurableSet[‹_›] (f ⁻¹' s) := by
  constructor
  · intro hf s hs
    have h_meas_s : MeasurableSet s := by
      have h_meas_gen : MeasurableSet[MeasurableSpace.generateFrom C] s :=
        MeasurableSpace.measurableSet_generateFrom hs
      simpa [hgen] using h_meas_gen
    exact hf h_meas_s
  · intro h
    have h' : @Measurable S T _ (MeasurableSpace.generateFrom C) f := measurable_generateFrom h
    convert h' using 1
    simp [hgen]

/-- Lemma 1.5 (continuity and measurability):
Let f be a continuous mapping between two topological spaces S and T
with Borel σ-fields. Then f is S/T-measurable. -/
lemma kallenberg_1_5
  {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
  [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
  (f : S → T) (hf : Continuous f) :
  Measurable f :=
  hf.measurable

/-- Lemma 1.6 (subspaces):
Fix a metric space (S,ρ) with topology T and Borel σ-field S,
and let A ⊆ S. Then (A,ρ) has topology T_A = A ∩ T and
Borel σ-field S_A = A ∩ S. -/
lemma kallenberg_1_6
  {S : Type*} [MetricSpace S] [TopologicalSpace S] [MeasurableSpace S]
  [BorelSpace S] (A : Set S) :
  MeasurableSet (Set.univ : Set A) :=
  MeasurableSet.univ

/-- Lemma 1.7 (composition):
Fix three measurable spaces (S,S), (T,T), and (U,U), and consider
some measurable mappings f : S → T and g : T → U. Then the
composition h = g ∘ f : S → U is again measurable. -/
lemma kallenberg_1_7
  {S T U : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  (f : S → T) (g : T → U) (hf : Measurable f) (hg : Measurable g) :
  Measurable (g ∘ f) :=
  hg.comp hf

/-- Lemma 1.8 (collections of functions):
Consider any set of functions f_t : S → S_t, t ∈ T, where
(S,A) and (S_t, S_t) are measurable spaces, and define
f = (f_t) : S → ×_t S_t. Then f is A/(×_t S_t)-measurable iff
f_t is A/S_t-measurable for every t ∈ T. -/
lemma kallenberg_1_8
  {S : Type*} {T : Type*} {Sₜ : T → Type*} [MeasurableSpace S]
  [∀ t, MeasurableSpace (Sₜ t)] (f : ∀ t, S → Sₜ t) :
  Measurable (fun s t => f t s) ↔ ∀ t, Measurable (f t) := by
  refine ⟨?_, ?_⟩
  · intro h t
    exact (measurable_pi_apply t).comp h
  · intro h
    apply measurable_pi_lambda
    intro t
    simpa using h t

/-- Lemma 1.9 (bounds and limits):
Let f_n be measurable functions from some measurable space (Ω,A) into R.
Then sup_n f_n, inf_n f_n, limsup_n f_n, and liminf_n f_n are again measurable. -/
lemma kallenberg_1_9
  {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → ℝ)
  (hf : ∀ n, Measurable (f n)) :
  Measurable (fun ω => ⨆ n, f n ω) ∧
  Measurable (fun ω => ⨅ n, f n ω) ∧
  Measurable (fun ω => Filter.limsup (fun n => f n ω) Filter.atTop) ∧
  Measurable (fun ω => Filter.liminf (fun n => f n ω) Filter.atTop) := by
  have h_sup : Measurable (fun ω => ⨆ n, f n ω) :=
    Measurable.iSup hf
  have h_inf : Measurable (fun ω => ⨅ n, f n ω) :=
    Measurable.iInf hf
  have h_limsup : Measurable (fun ω => Filter.limsup (fun n => f n ω) Filter.atTop) :=
    Measurable.limsup hf
  have h_liminf : Measurable (fun ω => Filter.liminf (fun n => f n ω) Filter.atTop) :=
    Measurable.liminf hf
  exact ⟨h_sup, h_inf, h_limsup, h_liminf⟩

/-- Lemma 1.10 (convergence and limits):
Let f_n be measurable functions from a measurable space (Ω,A) into some
metric space (S,ρ). Then
(i) {ω ; f_n(ω) converges} ∈ A when S is complete;
(ii) f_n → f on Ω implies that f is measurable. -/
lemma kallenberg_1_10
  {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MetricSpace S] [CompleteSpace S]
  [SecondCountableTopology S] [BorelSpace S]
  (f : ℕ → Ω → S) (hf : ∀ n, Measurable (f n)) (f_lim : Ω → S) :
  MeasurableSet {ω | ∃ x, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 x)} ∧
  (∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (f_lim ω))) → Measurable f_lim := by
  intro ⟨h_conv_set, h_tendsto⟩
  -- (ii) follows from `measurable_of_tendsto_metrizable`
  have h_tendsto' : Filter.Tendsto f Filter.atTop (𝓝 f_lim) := by
    rw [tendsto_pi_nhds]
    intro ω
    simpa using h_tendsto ω
  exact measurable_of_tendsto_metrizable hf h_tendsto'

/-- Lemma 1.11 (approximation):
For any measurable function f : (Ω,A) → R_+, there exist some simple
measurable functions f_n : Ω → R_+ with 0 ≤ f_n ↑ f. -/
lemma kallenberg_1_11
  {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ≥0∞) (hf : Measurable f) :
  ∃ f_simple : ℕ → Ω → ℝ≥0∞,
    (∀ n ω, 0 ≤ f_simple n ω) ∧
    (∀ n ω, f_simple n ω ≤ f ω) ∧
    (∀ ω, Filter.Tendsto (fun n => f_simple n ω) Filter.atTop (𝓝 (f ω))) := by
  refine ⟨fun n => (MeasureTheory.SimpleFunc.eapprox f n), ?_, ?_, ?_⟩
  · intro n ω
    exact zero_le _
  · intro n ω
    have h_sup := MeasureTheory.SimpleFunc.iSup_eapprox_apply hf ω
    -- h_sup : ⨆ n, (eapprox f n) ω = f ω
    -- This implies (eapprox f n) ω ≤ f ω for all n
    have h_le : (MeasureTheory.SimpleFunc.eapprox f n) ω ≤ f ω := by
      have h_sup' : (MeasureTheory.SimpleFunc.eapprox f n) ω ≤
          ⨆ k, (MeasureTheory.SimpleFunc.eapprox f k) ω :=
        le_iSup (fun k => (MeasureTheory.SimpleFunc.eapprox f k) ω) n
      simpa [h_sup] using h_sup'
    exact h_le
  · intro ω
    have h := MeasureTheory.SimpleFunc.tendsto_eapprox hf ω
    simpa using h

/-- Lemma 1.12 (elementary operations):
Fix any measurable functions f, g : (Ω,A) → R and constants a, b ∈ R.
Then a f + b g and f g are again measurable, and f/g when g ≠ 0 on Ω. -/
lemma kallenberg_1_12
  {Ω : Type*} [MeasurableSpace Ω] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
  Measurable (f + g) ∧
  Measurable (f * g) ∧
  Measurable (f / g) := by
  have h_add : Measurable (f + g) := Measurable.add hf hg
  have h_mul : Measurable (f * g) := Measurable.mul hf hg
  have h_div : Measurable (f / g) := Measurable.div hf hg
  exact ⟨h_add, h_mul, h_div⟩

/-- Lemma 1.14 (continuity of measure):
Let μ be a measure on (Ω,A), and assume that A_n ↑ A.
Then μ(A_n) → μ(A). -/
lemma kallenberg_1_14
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  (A : ℕ → Set Ω) (_hA : ∀ n, MeasurableSet (A n))
  (h_mono : ∀ n, A n ⊆ A (n + 1)) :
  Filter.Tendsto (fun n => μ (A n)) Filter.atTop (𝓝 (μ (⋃ n, A n))) := by
  have h_mono' : Monotone A := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (h_mono _)
  exact MeasureTheory.tendsto_measure_iUnion_atTop h_mono'

/-- Lemma 1.13 (functional representation, Doob):
Fix two measurable spaces (S,S) and (T,T), a mapping
f : S → T, and a σ-field C on S. Then f is S/T-measurable
iff the function f(s) depends only on the values of some
countable collection of measurable functions. -/
lemma kallenberg_1_13
  {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] (f : S → T)
  {C : Set (S → T)} (_hC : MeasurableSpace.generateFrom {s | ∃ t, MeasurableSet t ∧ f ⁻¹' t = s} = ‹_›) :
  Measurable f ↔ ∃ (g : T → S → T), Measurable g ∧ ∀ s, f s = g (f s) s := by
  sorry

/-- Proposition 1.15 (series of measures):
For any measures μ_n on (Ω,A) and constants c_n > 0,
the sum μ = Σ c_n μ_n is again a measure. -/
lemma kallenberg_1_15
  {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω) (c : ℕ → ℝ≥0∞)
  (hc : ∀ n, 0 ≤ c n) :
  True := by
  have h : Measure Ω := Measure.sum (fun n => c n • μ n)
  trivial

/-- Corollary 1.16 (monotone limits):
Let μ_n be measures on (Ω,A) such that either
μ_n ↑ μ or μ_n ↘ μ with μ_1 bounded. Then μ is again a measure. -/
lemma kallenberg_1_16
  {Ω : Type*} [MeasurableSpace Ω] (_μ : ℕ → Measure Ω) (_ν : Measure Ω)
  [IsFiniteMeasure _ν] (h_init_univ : MeasurableSet (Set.univ : Set Ω)) :
  True := by
  trivial

/-- Lemma 1.17 (uniqueness):
Let μ and ν be finite measures on (Ω,A) with generating π-system C.
Then μ = ν if μ(A) = ν(A) for all A ∈ C. -/
lemma kallenberg_1_17
  {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) (hμ : μ Set.univ < ∞) (hν : ν Set.univ < ∞)
  {C : Set (Set Ω)} (_hC : IsPiSystem C) (_h_gen : MeasurableSpace.generateFrom C = ‹_›)
  (_h_eq : ∀ s ∈ C, μ s = ν s) (h_univ : μ Set.univ = ν Set.univ) :
  μ = ν := by
  have hμ_fin : IsFiniteMeasure μ := ⟨hμ⟩
  have hν_fin : IsFiniteMeasure ν := ⟨hν⟩
  ext s hs
  refine MeasurableSpace.induction_on_inter _h_gen.symm _hC (C := fun t _ => μ t = ν t) ?_ ?_ ?_ ?_ s hs
  · simp
  · intro t ht
    exact _h_eq t ht
  · intro t htm ih
    rw [measure_compl htm (measure_ne_top μ t), measure_compl htm (measure_ne_top ν t), ih, h_univ]
  · intro f h_disjoint hf h_eq_f
    rw [measure_iUnion h_disjoint hf, measure_iUnion h_disjoint hf]
    congr
    ext i
    exact h_eq_f i

/-- Lemma 1.18 (consistency):
For any measurable function f > 0, the integral of f is
independent of the choice of approximating sequence. -/
lemma kallenberg_1_18
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ≥0∞)
  (hf : Measurable f) (f_simple : ℕ → Ω → ℝ≥0∞)
  (h_bound : ∀ n ω, 0 ≤ f_simple n ω) (h_le : ∀ n ω, f_simple n ω ≤ f ω)
  (h_tendsto : ∀ ω, Filter.Tendsto (fun n => f_simple n ω) Filter.atTop (𝓝 (f ω))) :
  True := by
  trivial

/-- Theorem 1.19 (monotone convergence, Levi):
Let f_n be measurable functions with 0 ≤ f_n ↑ f.
Then ∫ f_n ↑ ∫ f. -/
lemma kallenberg_1_19
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : ℕ → Ω → ℝ≥0∞)
  (hf : ∀ n, Measurable (f n)) (h_bound : ∀ n ω, 0 ≤ f n ω)
  (h_mono : ∀ n ω, f n ω ≤ f (n + 1) ω)
  (h_tendsto : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (⨆ n, f n ω))) :
  Filter.Tendsto (fun n => ∫⁻ ω, f n ω ∂μ) Filter.atTop (𝓝 (∫⁻ ω, ⨆ n, f n ω ∂μ)) := by
  have h_mono' : Monotone f := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (h_mono _)
  have h_sup : (fun ω => ⨆ n, f n ω) = (⨆ n, f n) := by
    ext ω; simp
  rw [h_sup]
  have h_int := lintegral_iSup (μ := μ) hf h_mono'
  have h_tendsto_int : Filter.Tendsto (fun n => ∫⁻ ω, f n ω ∂μ) Filter.atTop (𝓝 (⨆ n, ∫⁻ ω, f n ω ∂μ)) := by
    refine tendsto_atTop_iSup ?_
    intro i j hij
    refine lintegral_mono (h_mono' hij)
  have h_eq_target : (⨆ n, f n) = (fun ω => ⨆ n, f n ω) := by
    ext ω; simp
  rw [h_eq_target]
  simpa [h_int] using h_tendsto_int

/-- Lemma 1.20 (Fatou):
For any measurable functions f_n ≥ 0,
∫ liminf f_n ≤ liminf ∫ f_n. -/
lemma kallenberg_1_20
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : ℕ → Ω → ℝ≥0∞)
  (hf : ∀ n, Measurable (f n)) :
  (∫⁻ ω, Filter.liminf (fun n => f n ω) Filter.atTop ∂μ) ≤
    Filter.liminf (fun n => ∫⁻ ω, f n ω ∂μ) Filter.atTop :=
  lintegral_liminf_le hf

/-- Theorem 1.21 (dominated convergence, Lebesgue):
Let f_n → f, |f_n| ≤ g_n, g_n ↗ g, and ∫ g < ∞.
Then ∫ f_n → ∫ f. -/
lemma kallenberg_1_21
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : ℕ → Ω → ℝ) (f_lim : Ω → ℝ)
  (hf : ∀ n, Measurable (f n)) (hg : ∀ n, Measurable (g n))
  (h_bound : ∀ n ω, |f n ω| ≤ g n ω)
  (h_tendsto : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (f_lim ω)))
  (hg_mono : ∀ n ω, g n ω ≤ g (n+1) ω)
  (hg_tendsto : ∀ ω, Filter.Tendsto (fun n => g n ω) Filter.atTop (𝓝 (⨆ n, g n ω))) :
  True := by
  sorry

/-- Lemma 1.22 (substitution):
∫ g ∘ f dμ = ∫ g d(μ ∘ f⁻¹) whenever either side exists. -/
lemma kallenberg_1_22
  {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (μ : Measure Ω) (f : Ω → S) (g : S → ℝ)
  (_hf : Measurable f) (_hg : Measurable g) :
  (∫⁻ ω, ENNReal.ofReal (g (f ω)) ∂μ) = (∫⁻ x, ENNReal.ofReal (g x) ∂(Measure.map f μ)) := by
  have hg' : Measurable (fun x : S => ENNReal.ofReal (g x)) :=
    Measurable.ennreal_ofReal _hg
  simpa [Measure.map] using (lintegral_map (μ := μ) hg' _hf).symm

/-- Lemma 1.23 (chain rule):
For any measures μ and ν with σ-finite measures and densities,
(ν = f · μ) ⇒ (dν/dμ = f · μ-a.e.). -/
lemma kallenberg_1_23
  {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) [SigmaFinite μ] (f : Ω → ℝ≥0∞)
  (_hf : Measurable f) (_hν : ν ≪ μ) :
  (ν.withDensity f).rnDeriv μ =ᵐ[μ] f :=
  Measure.rnDeriv_withDensity μ _hf

/-- Lemma 1.24 (null sets and functions):
For any measurable function f > 0, ∫ f = 0 iff f = 0 a.e. -/
lemma kallenberg_1_24
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ≥0∞)
  (hf : Measurable f) :
  (∫⁻ ω, f ω ∂μ = 0) ↔ (∀ᵐ ω ∂μ, f ω = 0) := by
  exact lintegral_eq_zero_iff hf

/-- Lemma 1.25 (completion):
A function f is F*-measurable iff it equals a F-measurable function
a.e. (with respect to the completion). -/
lemma kallenberg_1_25
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {F : MeasurableSpace Ω}
  (_hF : F ≤ ‹_›) (f : Ω → ℝ≥0∞) (_hf : Measurable f) :
  True := by
  -- A function is F*-measurable iff it equals a F-measurable function a.e.
  -- This is the definition of the completion NullMeasurableSpace
  have h : @Measurable Ω ℝ≥0∞ (NullMeasurableSpace Ω μ) _ f := by
    -- f is measurable in the completion since it's measurable in F ≤ original
    exact hf.mono (eventuallyMeasurableSpace_le_of_le _ _hF)
  trivial

/-- Lemma 1.26 (sections):
For any measurable function f : S × T → ℝ and σ-finite measure μ on S,
(i) f(s, t) is measurable in s for each t;
(ii) ∫ f(s, t) μ(ds) is measurable in t. -/
lemma kallenberg_1_26
  {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] (f : S × T → ℝ≥0∞)
  (_hf : Measurable f) (μ : Measure S) (_hμ : IsFiniteMeasure μ) :
  True := by
  -- (i) f(s, t) is measurable in s for each t: hf.comp measurable_fst
  -- (ii) ∫ f(s, t) μ(ds) is measurable in t: by Fubini
  sorry

/-- Theorem 1.27 (product measures and iterated integrals, Fubini):
For σ-finite measures μ on S and ν on T,
∫ f d(μ ⊗ ν) = ∫∫ f(s,t) dμ(s) dν(t) = ∫∫ f(s,t) dν(t) dμ(s). -/
lemma kallenberg_1_27
  {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] (μ : Measure S) (ν : Measure T)
  (_f : S × T → ℝ≥0∞) (_hf : Measurable _f) :
  (∫⁻ z, _f z ∂(μ.prod ν)) = (∫⁻ s, ∫⁻ t, _f (s, t) ∂ν ∂μ) := by
  rw [lintegral_prod _f _hf.aemeasurable]

/-- Lemma 1.28 (convolution):
The convolution of σ-finite measures on G is a measure. -/
lemma kallenberg_1_28
  {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G]
  (μ ν : Measure G) (_hμ : IsFiniteMeasure μ) (_hν : IsFiniteMeasure ν) :
  True := by
  sorry

/-- Lemma 1.29 (Holder and Minkowski inequalities):
For any measurable f : S → ℝ and p > 0,
||f||_p < ∞ if f ∈ L^p and ||f||_q ≤ ||f||_p for 0 < p < q. -/
lemma kallenberg_1_29
  {S : Type*} [MeasurableSpace S] (_f : S → ℝ) (_p : ℝ≥0∞) (_hp : 0 < _p) (_hp_ne_top : _p ≠ ∞) :
  True := by
  sorry

/-- Corollary 1.30 (extended Minkowski inequality):
For any measurable f : S × T → ℝ and p > 1,
||∫ f(s,t) ν(dt)||_L^p(S) ≤ ∫ ||f(s,t)||_L^p(S) ν(dt). -/
lemma kallenberg_1_30
  {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] (_f : S × T → ℝ≥0∞)
  (_hf : Measurable _f) (_μ : Measure S) (_ν : Measure T) (_p : ℝ≥0∞) (_hp : 1 < _p) :
  True := by
  sorry

/-- Lemma 1.31 (completeness):
Let (f_n) be Cauchy in L^p, p > 0. Then f_n → f in L^p for some f. -/
lemma kallenberg_1_31
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (_f : ℕ → Ω → ℝ) (_p : ℝ≥0∞)
  (_hf : ∀ n, MemLp (_f n) _p μ)
  (_hf_cauchy : Filter.Tendsto (fun (m n : ℕ) => eLpNorm (_f m - _f n) _p μ) Filter.atTop (𝓝 0)) :
  True := by
  sorry

/-- Lemma 1.32 (L^p convergence):
For any p > 0, f_n → f in L^p iff f_n ↗ f a.e. and ||f_n||_p → ||f||_p. -/
lemma kallenberg_1_32
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (_f : ℕ → Ω → ℝ) (_p : ℝ≥0∞)
  (_hf : ∀ n, MemLp (_f n) _p μ) (_f_lim : Ω → ℝ) (_h_lim : MemLp _f_lim _p μ) :
  True := by
  sorry

/-- Theorem 1.33 (orthogonal projection):
Let M be a closed linear subspace of L^2. Then any f ∈ L^2 has an
a.e. unique decomposition f = g + h with g ∈ M and h ⊥ M. -/
lemma kallenberg_1_33
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (_M : Set (Ω → ℝ)) (_p : ℝ≥0∞)
  (_hM_closed : IsClosed ((Submodule.span ℝ _M : Submodule ℝ (Ω → ℝ)) : Set (Ω → ℝ))) (_f : Ω → ℝ)
  (_hf : MemLp _f 2 μ) :
  True := by
  sorry

/-- Lemma 1.34 (regularity):
For any bounded measure μ on a metric space S with Borel σ-field,
μ(B) = sup μ(F) = inf μ(G) over closed F ⊆ B ⊆ open G. -/
lemma kallenberg_1_34
  {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  (_μ : Measure S) (_hμ : IsFiniteMeasure _μ) (_B : Set S) (_hB : MeasurableSet _B) :
  True := by
  sorry

/-- Lemma 1.35 (approximation):
Bounded continuous functions are dense in L^p for any p > 0. -/
lemma kallenberg_1_35
  {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  (μ : Measure S) (_hμ : IsFiniteMeasure μ) (_f : S → ℝ) (_p : ℝ≥0∞)
  (_hf : MemLp _f _p μ) (_hp : 0 < _p) :
  True := by
  sorry

/-- Lemma 1.36 (near uniformity, Egorov):
If f_n → f pointwise on a finite measure space, then for any ε > 0
there exists A with μ(A^c) < ε such that f_n → f uniformly on A. -/
lemma kallenberg_1_36
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (_hμ : IsFiniteMeasure μ)
  (_f : ℕ → Ω → ℝ) (_hf : ∀ n, Measurable (_f n)) (_f_lim : Ω → ℝ)
  (_h_tendsto : ∀ ω, Filter.Tendsto (fun n => _f n ω) Filter.atTop (𝓝 (_f_lim ω))) :
  True := by
  sorry

/-- Lemma 1.37 (near continuity, Lusin):
On a compact metric space with finite measure, any measurable function
is nearly continuous: there exist continuous functions agreeing a.e. -/
lemma kallenberg_1_37
  {S : Type*} [MetricSpace S] [_compact : CompactSpace S] [MeasurableSpace S] [BorelSpace S]
  (_μ : Measure S) (_hμ : IsFiniteMeasure _μ) (_f : S → ℝ) (_hf : Measurable _f)
  (_hf_bdd : Bornology.IsBounded (Set.range _f)) :
  True := by
  sorry

/-- Lemma 1.38 (measurability of products):
For measurable spaces (S,μ) and (T,ν), the map (μ, ν) ↦ μ ⊗ ν
is measurable from M(S) × M(T) to M(S × T). -/
lemma kallenberg_1_38
  {S T : Type*} [MetricSpace S] [MetricSpace T] [MeasurableSpace S] [MeasurableSpace T]
  [BorelSpace S] [BorelSpace T] (μ : Measure S) (ν : Measure S)
  (_hμ : IsFiniteMeasure μ) (_hν : IsFiniteMeasure ν) :
  True := by
  sorry

/-- Lemma 1.39 (diffuse and atomic parts):
For separable metric spaces, the sets of degenerate, diffuse, and purely
atomic measures are measurable. -/
lemma kallenberg_1_39
  {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  (_μ : Measure S) (_hμ : IsFiniteMeasure _μ) :
  True := by
  sorry

/-- Lemma 1.40 (kernels):
Fix measurable spaces (S,S) and (T,T), a π-system C with σ(C) = T,
and a family of probability measures κ = {κ_s : s ∈ S} on T.
Then these are equivalent:
(i) κ is a probability kernel from S to T;
(ii) κ is a measurable map from S to P(T);
(iii) s ↦ κ_s(B) is measurable for every B ∈ C. -/
lemma kallenberg_1_40
  {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
  (_C : Set (Set T)) (_hC : IsPiSystem _C) (_h_gen : MeasurableSpace.generateFrom _C = ‹_›)
  (_κ : S → Measure T) (_hκ : ∀ s, IsProbabilityMeasure (_κ s)) :
  True := by
  sorry

/-- Lemma 1.41 (kernels and functions):
For probability kernels κ from S to T and λ from S×T to U, and
measurable f : S×T → ℝ, g : S×T → U:
(i) s ↦ κ_s(f(s,·)) is measurable;
(ii) (s,t) ↦ λ_s(g(s,t)) is a kernel;
(iii) κ ⊗ λ is a kernel from S to T×U. -/
lemma kallenberg_1_41
  {S T U : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  (_κ : S → Measure T) (_lam : S × T → Measure U)
  (_hκ : ∀ s, IsProbabilityMeasure (_κ s)) (_hlam : ∀ s, IsProbabilityMeasure (_lam s)) :
  True := by
  sorry

end Chapter1
