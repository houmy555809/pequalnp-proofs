import Mathlib

theorem PEqualNP.Outside.L_twin_primes_zero_extension :
    ∀ (N : ℕ) (b : ℤ → ℝ), (∀ n, n < 0 ∨ (N:ℤ) < n → b n = 0) → let S := Finset.Icc (-2:ℤ) (N:ℤ); S.sum (fun n => (b n+b (n+2))^2) - S.sum (fun n => (b n-b (n+2))^2) = 4*S.sum (fun n => b n*b (n+2)) := by
  intro N b hb
  dsimp only
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring
