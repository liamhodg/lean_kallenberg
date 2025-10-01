import Mathlib.MeasureTheory.Measure.MeasureSpace

open Set MeasureTheory

variable {α : Type*} [MeasurableSpace α]

notation s " ∆ " t => symmDiff s t

lemma exercise_1_1 (μ : Measure α) (A B C : Set α) :
  μ (A ∆ C) ≤ μ (A ∆ B) + μ (B ∆ C) := by
  have hsubset : (A ∆ C) ⊆ (A ∆ B) ∪ (B ∆ C) := by
    intro x hx
    have hx' : x ∈ (A \ C) ∪ (C \ A) := by simpa using hx
    rcases hx' with hxAC | hxCA
    · rcases hxAC with ⟨hxA, hnotC⟩
      by_cases hxB : x ∈ B
      · exact Or.inr <| Or.inl ⟨hxB, hnotC⟩
      · exact Or.inl <| Or.inl ⟨hxA, hxB⟩
    · rcases hxCA with ⟨hxC, hnotA⟩
      by_cases hxB : x ∈ B
      · exact Or.inl <| Or.inr ⟨hxB, hnotA⟩
      · exact Or.inr <| Or.inr ⟨hxC, hxB⟩
  -- Using monotonicity
  calc
    μ (A ∆ C) ≤ μ ((A ∆ B) ∪ (B ∆ C)) := measure_mono hsubset
    _         ≤ μ (A ∆ B) + μ (B ∆ C) := measure_union_le _ _

-- Show that Lemma 1.10 fails for uncountable index sets. (Hint: Show that
-- every measurable set depends on countably many coordinates.)
