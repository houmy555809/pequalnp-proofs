import Mathlib

theorem PEqualNP.Outside.L_twin_primes_mangoldt_divisors :
    ∀ n : ℕ, 0 < n → ArithmeticFunction.vonMangoldt n = n.divisors.sum (fun d => -(ArithmeticFunction.moebius d : ℝ)*Real.log d) := by
  intro n hn
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  simp only [ArithmeticFunction.log_apply] at h
  have hR : n.divisors.sum (fun d => -(ArithmeticFunction.moebius d : ℝ) * Real.log d)
      = -(n.divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log d)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hR, h]
  ring
