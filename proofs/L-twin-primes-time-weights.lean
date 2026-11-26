import Mathlib

theorem PEqualNP.Outside.L_twin_primes_time_weights :
    ∀ (l : ℝ → ℝ) (t : ℝ), let g := fun (σ : ℝ) => (l t)^2 * (1+σ*Real.cos (4*Real.pi*t)); 0 ≤ g 1 ∧ 0 ≤ g (-1) ∧ g 1 - g (-1) = 2*(l t)^2*Real.cos (4*Real.pi*t) := by
  intro l t
  dsimp only
  have h1 : -1 ≤ Real.cos (4 * Real.pi * t) := Real.neg_one_le_cos _
  have h2 : Real.cos (4 * Real.pi * t) ≤ 1 := Real.cos_le_one _
  refine ⟨?_, ?_, ?_⟩
  · refine mul_nonneg (sq_nonneg _) ?_
    linarith
  · refine mul_nonneg (sq_nonneg _) ?_
    linarith
  · ring
