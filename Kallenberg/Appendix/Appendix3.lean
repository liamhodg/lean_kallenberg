import Mathlib

open Set
open scoped RealInnerProductSpace

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
  -- Split into the easy empty-interior case and the interesting one.
  by_cases hInt : (interior M).Nonempty
  · set s := interior M
    have hConvInt : Convex ℝ s := hM.interior
    have hsOpen : IsOpen s := isOpen_interior
    -- Work inside the open convex subset `s = interior M`.
    -- Afterwards we transfer the inequalities back to `M`
    -- using `closure_interior_eq_closure_of_nonempty_interior`.
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
    -- Strict separation on the interior propagates to the boundary via openness.
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
      -- Replace `closure M` by `closure s` so that we can use the supporting-open-set argument.
      simpa [s, hclosure] using hy_closureM
    rcases (mem_closure_iff.1 hy_closure_s) U hUopen hyU with ⟨z, hzU, hzs⟩
    -- The cluster point contradicts the strict inequality on `s`.
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
    -- With empty interior the statement is vacuous, so the zero functional suffices.
    intro _ _; simp

/-- Corollary A3.2(ii) (separation of convex sets).
Two disjoint convex subsets of `E` can be separated by a continuous linear functional. -/
lemma kallenberg_a3_2_ii {M N : Set E} (hM : Convex ℝ M) (hN : Convex ℝ N)
    (hdisj : Disjoint M N) :
    ∃ (φ : StrongDual ℝ E) (b : ℝ), (∀ y ∈ M, φ y ≤ b) ∧ (∀ y ∈ N, b ≤ φ y) := by
  classical
  -- First, try to find support at a boundary point of `M`.
  by_cases hIntM : (interior M).Nonempty
  · set s := interior M
    have hConv_s : Convex ℝ s := hM.interior
    have hOpen_s : IsOpen s := isOpen_interior
    have hdisj_sN : Disjoint s N := hdisj.mono_left interior_subset
    obtain ⟨φ, u, hφ_s, hφ_N⟩ :=
      geometric_hahn_banach_open (s := s) (t := N) hConv_s hOpen_s hN hdisj_sN
    refine ⟨φ, u, ?_, hφ_N⟩
    intro y hyM
    -- Access to the open-set separator requires approximating `y` by points in `s`.
    have hy_closure_s : y ∈ closure s := by
      have hy_closureM : y ∈ closure M := subset_closure hyM
      have hclosure :=
        hM.closure_interior_eq_closure_of_nonempty_interior (𝕜 := ℝ) hIntM
      simpa [s, hclosure] using hy_closureM
    by_contra h_gt
    -- As in part (i), build a strict bump above `u` and contradict the open separation.
    have hlt : u < φ y := lt_of_not_ge h_gt
    set δ := (φ y - u) / 2
    have hδpos : 0 < δ := by
      have : φ y - u > 0 := sub_pos.mpr hlt
      simpa [δ] using half_pos this
    have hy_sub_pos : 0 < φ y - u := sub_pos.mpr hlt
    have hhalf : δ < φ y - u := by simpa [δ] using (half_lt_self hy_sub_pos)
    have hy_mem : u + δ < φ y := by
      have := add_lt_add_left hhalf u
      simpa [δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    let U := (fun z : E => φ z) ⁻¹' Set.Ioi (u + δ)
    have hUopen : IsOpen U := φ.continuous.isOpen_preimage _ isOpen_Ioi
    have hyU : y ∈ U := by simpa [U, Set.mem_preimage, Set.mem_Ioi] using hy_mem
    obtain ⟨z, hzU, hzs⟩ := (mem_closure_iff.1 hy_closure_s) U hUopen hyU
    have hz_gt : φ z ∈ Set.Ioi (u + δ) := by
      -- Because `U` is an open strict upper halfspace, its points stay strictly above `u`.
      simpa [U, Set.mem_preimage] using hzU
    have hz_gt' : u < φ z := by
      have huv : u < u + δ := lt_add_of_pos_right _ hδpos
      have : u + δ < φ z := by simpa [Set.mem_Ioi] using hz_gt
      exact lt_trans huv this
    have hz_lt : φ z < u := hφ_s z hzs
    exact (lt_irrefl _ (lt_trans hz_gt' hz_lt))
  -- Otherwise we pass to the other set and point the functional in the opposite direction.
  · by_cases hIntN : (interior N).Nonempty
    · set s := interior N
      have hConv_s : Convex ℝ s := hN.interior
      have hOpen_s : IsOpen s := isOpen_interior
      have hdisj_sM : Disjoint s M := hdisj.symm.mono_left interior_subset
      obtain ⟨φ, u, hφ_s, hφ_M⟩ :=
        geometric_hahn_banach_open (s := s) (t := M) hConv_s hOpen_s hM hdisj_sM
      refine ⟨-φ, -u, ?_, ?_⟩
      · intro y hyM
        -- Translate the inequality `φ y ≤ u` into the inequality required for `-φ`.
        have hy := hφ_M y hyM
        have : -φ y ≤ -u := neg_le_neg hy
        simpa using this
      · intro y hyN
        have hy_closure_s : y ∈ closure s := by
          -- Mirror the closure argument on `N` to find interior approximants of `y`.
          have hy_closureN : y ∈ closure N := subset_closure hyN
          have hclosure :=
            hN.closure_interior_eq_closure_of_nonempty_interior (𝕜 := ℝ) hIntN
          simpa [s, hclosure] using hy_closureN
        have hy_le : φ y ≤ u := by
          by_contra h_gt
          -- Again use the open-set separation to get a contradiction.
          have hlt : u < φ y := lt_of_not_ge h_gt
          set δ := (φ y - u) / 2
          have hδpos : 0 < δ := by
            have : φ y - u > 0 := sub_pos.mpr hlt
            simpa [δ] using half_pos this
          have hy_sub_pos : 0 < φ y - u := sub_pos.mpr hlt
          have hhalf : δ < φ y - u := by simpa [δ] using (half_lt_self hy_sub_pos)
          have hy_mem : u + δ < φ y := by
            have := add_lt_add_left hhalf u
            simpa [δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
          let U := (fun z : E => φ z) ⁻¹' Set.Ioi (u + δ)
          have hUopen : IsOpen U := φ.continuous.isOpen_preimage _ isOpen_Ioi
          have hyU : y ∈ U := by simpa [U, Set.mem_preimage, Set.mem_Ioi] using hy_mem
          obtain ⟨z, hzU, hzs⟩ := (mem_closure_iff.1 hy_closure_s) U hUopen hyU
          have hz_gt : φ z ∈ Set.Ioi (u + δ) := by
            -- The same open-halfspace argument gives a point strictly above `u`.
            simpa [U, Set.mem_preimage] using hzU
          have hz_gt' : u < φ z := by
            have huv : u < u + δ := lt_add_of_pos_right _ hδpos
            have : u + δ < φ z := by simpa [Set.mem_Ioi] using hz_gt
            exact lt_trans huv this
          have hz_lt : φ z < u := hφ_s z hzs
          exact (lt_irrefl _ (lt_trans hz_gt' hz_lt))
        have : -u ≤ -φ y := by
          simpa [neg_le_neg_iff] using hy_le
        simpa using this
    · refine ⟨0, 0, ?_, ?_⟩
      -- If both interiors are empty, the desired non-strict inequalities are automatic.
      · intro _ _; simp
      · intro _ _; simp

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
  refine ⟨NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E), ?_⟩
  intro x f
  change NormedSpace.inclusionInDoubleDual (𝕜 := ℝ) (E := E) x f = f x
  simp [NormedSpace.dual_def]  -- direct evaluation of the inclusion map


def weakStarTopologyOnDual (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopologicalSpace (StrongDual ℝ E) :=
  TopologicalSpace.induced (fun φ : StrongDual ℝ E => fun x : E => φ x)
    (inferInstance : TopologicalSpace (E → ℝ))

def weakTopologyOnDual (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopologicalSpace (StrongDual ℝ E) :=
  TopologicalSpace.induced
    (fun φ : StrongDual ℝ E => fun ψ : StrongDual ℝ (StrongDual ℝ E) => ψ φ)
    (inferInstance : TopologicalSpace (StrongDual ℝ (StrongDual ℝ E) → ℝ))

/-- Lemma A3.5(i) (topologies on X*)
For a normed linear space X, write Tw*, Tw, Tn for the weak*, weak, and
norm topologies on X*. Then Tw* ⊆ Tw ⊆ Tn -/
lemma kallenberg_a3_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    weakStarTopologyOnDual E ≤ weakTopologyOnDual E ∧
      weakTopologyOnDual E ≤
        (UniformSpace.toTopologicalSpace : TopologicalSpace (StrongDual ℝ E)) := by
  classical
  sorry

/-- Lemma A3.5(ii) (topologies on X*)
For a normed reflexive linear space X, the weak*, weak, and norm topologies
on X* are equivalent. -/
lemma kallenberg_a3_5_ii {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h_reflexive : Function.Surjective
      (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E))) :
    weakStarTopologyOnDual E = weakTopologyOnDual E ∧
      weakTopologyOnDual E =
        (UniformSpace.toTopologicalSpace : TopologicalSpace (StrongDual ℝ E)) := by
  classical
  sorry


/-- Lemma A3.6 (Riesz representation)
For functions f on a Hilbert space H, f is a continuous linear functional
on H if and only if there exists a unique element y ∈ H such that
f(x) = ⟨x, y⟩ for all x ∈ H. In this case, ‖f‖ = ‖y‖. -/
lemma kallenberg_a3_6
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E →L[ℝ] ℝ) :
    ∃! y : E,
      (∀ x : E, f x = Inner.inner (𝕜 := ℝ) x y) ∧ ‖f‖ = ‖y‖ := by
  classical
  set y := (InnerProductSpace.toDual ℝ E).symm f
  have hy : (InnerProductSpace.toDual ℝ E) y = f := by simp [y]
  refine ⟨y, ?_, ?_⟩
  constructor
  · intro x
    have hx := congrArg (fun g : StrongDual ℝ E => g x) hy
    have hx_comm : f x = Inner.inner (𝕜 := ℝ) y x := by
      simpa [InnerProductSpace.toDual_apply] using hx.symm
    simpa [real_inner_comm] using hx_comm
  · have hnorm : ‖(InnerProductSpace.toDual ℝ E) y‖ = ‖y‖ :=
      (InnerProductSpace.toDual ℝ E).norm_map' y
    simpa [hy] using hnorm
  · intro z hz
    obtain ⟨hz_eval, _⟩ := hz
    have hz' : (InnerProductSpace.toDual ℝ E) z = f := by
      ext x
      simpa [InnerProductSpace.toDual_apply, real_inner_comm] using (hz_eval x).symm
    have : z = (InnerProductSpace.toDual ℝ E).symm ((InnerProductSpace.toDual ℝ E) z) := by
      simp
    simpa [y, hy, hz'] using this

end Appendix3
