import Mathlib

theorem PEqualNP.Outside.L_twin_primes_theta_error_budget :
    ∀ (A P M Q N C E e f : ℝ), 0 < A → |(P-Q)/A-4*C| ≤ E → |P/A-M| ≤ e → |Q/A-N| ≤ f → (M-N-E-e-f)/4 ≤ C := by

  intro A P M Q N C E e f hA h1 h2 h3
  have h1a : (P-Q)/A - 4*C ≤ E := (abs_le.mp h1).2
  have h2b : -e ≤ P/A - M := (abs_le.mp h2).1
  have h3a : Q/A - N ≤ f := (abs_le.mp h3).2
  have hsplit : (P-Q)/A = P/A - Q/A := by ring
  rw [hsplit] at h1a
  linarith