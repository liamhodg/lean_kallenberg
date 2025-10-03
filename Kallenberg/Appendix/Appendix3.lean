import Mathlib

open Set

namespace Appendix3

/-- A convex functional on a real vector space is a positively
homogeneous and subadditive map. -/
structure ConvexFunctional (E : Type*) [AddCommGroup E] [Module ℝ E] where
  toFun : E → ℝ
  posHom : ∀ c > 0, ∀ x, toFun (c • x) = c * toFun x
  add_le : ∀ x y, toFun (x + y) ≤ toFun x + toFun y

instance (E : Type*) [AddCommGroup E] [Module ℝ E] :
    CoeFun (ConvexFunctional E) (fun _ => E → ℝ) :=
  ⟨ConvexFunctional.toFun⟩

/-- Lemma A3.1 (Hahn–Banach).
Let X be a linear space with subspace Y, fix a convex functional
p on X, and let f be a linear functional on Y with f ≤ p on Y.
Then f extends to a linear functional on X, such that
f ≤ p on X. -/
lemma kallenberg_a3_1
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ConvexFunctional E)
    (Y : Subspace ℝ E) (f : Y →ₗ[ℝ] ℝ)
    (hf : ∀ y : Y, f y ≤ p y) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x, g x ≤ p x) ∧ ∀ y : Y, g y = f y := by
  let fPMap : E →ₗ.[ℝ] ℝ := ⟨Y, f⟩
  have hf' : ∀ x : fPMap.domain, fPMap x ≤ p x := by
    intro x
    simpa using hf x
  obtain ⟨g, h_ext, h_le⟩ :=
    exists_extension_of_le_sublinear fPMap p
      (fun c hc x => p.posHom c hc x)
      (fun x y => p.add_le x y)
      hf'
  refine ⟨g, h_le, ?_⟩
  intro y
  simpa using h_ext y

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Corollary A3.2(i) (supporting hyperplane).
For a convex set `M ⊆ E` and a point `x ∈ ∂M`, there exists a
continuous linear functional whose level set through `x`
supports `M`. -/
lemma kallenberg_a3_2_i {M : Set E} (hM : Convex ℝ M) {x : E} (hx : x ∈ frontier M) :
    ∃ (φ : StrongDual ℝ E) (b : ℝ), φ x = b ∧ ∀ y ∈ M, φ y ≤ b := by
  classical
  by_cases hInt : (interior M).Nonempty
  · set s := interior M
    have hConvInt : Convex ℝ s := hM.interior
    have hsOpen : IsOpen s := isOpen_interior
    have hclosure :=
      hM.closure_interior_eq_closure_of_nonempty_interior (𝕜 := ℝ) hInt
    have hx_not_int : x ∉ s := by
      have hx_mem : x ∈ closure M ∩ closure (Mᶜ) := by
        simpa [frontier_eq_closure_inter_closure] using hx
      rcases hx_mem with ⟨_, hx_closure_compl⟩
      have hx_not : x ∉ interior M := by
        simpa [closure_compl] using hx_closure_compl
      simpa [s] using hx_not
    obtain ⟨φ, hφ_lt⟩ :=
      geometric_hahn_banach_open_point (s := s) hConvInt hsOpen hx_not_int
    refine ⟨φ, φ x, rfl, ?_⟩
    intro y hyM
    by_contra h_le
    have hy_lt : φ x < φ y := lt_of_not_ge h_le
    have hy_sub_pos : 0 < φ y - φ x := sub_pos.mpr hy_lt
    set δ := (φ y - φ x) / 2
    have hδpos : 0 < δ := by
      simpa [δ] using half_pos hy_sub_pos
    have hy_half : δ < φ y - φ x := by
      have := half_lt_self hy_sub_pos
      simpa [δ] using this
    have hyU' : φ x + δ < φ y := by
      have := add_lt_add_left hy_half (φ x)
      simpa [δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    let U := (fun z : E => φ z) ⁻¹' Set.Ioi (φ x + δ)
    have hUopen : IsOpen U := φ.continuous.isOpen_preimage _ isOpen_Ioi
    have hyU : y ∈ U := by
      simpa [U, Set.mem_preimage, Set.mem_Ioi] using hyU'
    have hy_closure_s : y ∈ closure s := by
      have hy_closureM : y ∈ closure M := subset_closure hyM
      simpa [s, hclosure] using hy_closureM
    rcases (mem_closure_iff.1 hy_closure_s) U hUopen hyU with ⟨z, hzU, hzs⟩
    have hz_gt : φ x + δ < φ z := by
      simpa [U, Set.mem_preimage, Set.mem_Ioi] using hzU
    have hz_lt : φ z < φ x := hφ_lt z hzs
    have h_contr : φ x + δ < φ x := lt_trans hz_gt hz_lt
    have hδneg : δ < 0 := by
      have h' : φ x + δ < φ x + 0 := by simpa using h_contr
      exact lt_of_add_lt_add_left h'
    have hzero : (0 : ℝ) < 0 := lt_trans hδpos hδneg
    exact (lt_irrefl _ hzero)
  · refine ⟨0, 0, by simp, ?_⟩
    intro _ _; simp

/-- Corollary A3.2(ii) (separation of convex sets).
Two disjoint convex subsets of `E` can be separated by a continuous linear functional. -/
lemma kallenberg_a3_2_ii {M N : Set E} (hM : Convex ℝ M) (hN : Convex ℝ N)
    (hdisj : Disjoint M N) :
    ∃ (φ : StrongDual ℝ E) (b : ℝ), (∀ y ∈ M, φ y ≤ b) ∧ (∀ y ∈ N, b ≤ φ y) := by
  classical
  sorry

/-- Theorem A3.3 (Hahn–Banach).
Let X be a normed linear space with a subspace Y. Then for
any g ∈ Y*, there exists an f ∈ X* with ‖f‖ = ‖g‖ and f = g
on Y. -/
theorem kallenberg_a3_3 {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : Subspace ℝ E) (g : StrongDual ℝ Y) :
    ∃ f : StrongDual ℝ E, (∀ y : Y, f y = g y) ∧ ‖f‖ = ‖g‖ := by
  simpa using Real.exists_extension_norm_eq (p := Y) g

/-- Corollary A3.4 (natural embedding).
For a normed linear space X, we may define a linear isometry
T : X → X** by (Tx)f = f(x) for x ∈ X, f ∈ X*. -/
theorem kallenberg_a3_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ T : E →ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ E),
      ∀ x (f : StrongDual ℝ E), T x f = f x := by
  sorry

end Appendix3
