import Mathlib

theorem PEqualNP.Outside.L_twin_primes_rh_contour :
    RiemannHypothesis → ∀ s : ℂ, 9/16 ≤ s.re → s.re < 1 → riemannZeta s ≠ 0 := by

  intro hRH s h1 h2 hz
  have hne1 : s ≠ 1 := by
    intro h
    rw [h] at h2
    norm_num at h2
  have hneg : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      push_cast
      norm_num
    rw [hre] at h1
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    nlinarith
  have hre := hRH s hz hneg hne1
  linarith