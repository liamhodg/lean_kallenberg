import Mathlib

open Set

namespace Appendix4

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Theorem A4.1 (Banach-Steinhaus)
Let T be a set of bounded linear operators from X to Y for a
Banach space X and a normed linear space Y. If
{‖Ax‖ : A ∈ T} is bounded for all x ∈ X, then
{‖A‖ : A ∈ T} is also bounded. -/
theorem kallenberg_a4_1
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : Set (X →L[ℝ] Y))
    (hT : ∀ x : X, ∃ C : ℝ, ∀ A ∈ T, ‖A x‖ ≤ C)
    : ∃ C : ℝ, ∀ A ∈ T, ‖A‖ ≤ C := by
  let g : {A : X →L[ℝ] Y // A ∈ T} → X →L[ℝ] Y := fun A => A
  have hg : ∀ x : X, ∃ C : ℝ, ∀ i : {A : X →L[ℝ] Y // A ∈ T}, ‖g i x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := hT x
    refine ⟨C, ?_⟩
    intro i
    simpa [g] using hC i.1 i.2
  obtain ⟨C, hC⟩ :=
    banach_steinhaus (E := X) (F := Y) (σ₁₂ := RingHom.id ℝ) (g := g) hg
  refine ⟨C, ?_⟩
  intro A hA
  simpa [g] using hC ⟨A, hA⟩

end Appendix4
