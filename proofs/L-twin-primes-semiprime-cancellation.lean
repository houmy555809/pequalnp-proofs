import Mathlib

theorem PEqualNP.Outside.L_twin_primes_semiprime_cancellation :
    ∀ r q : ℕ, r.Prime → q.Prime → r ≠ q → (r*q).divisors.sum (fun d => -(ArithmeticFunction.moebius d : ℝ)*Real.log d) = 0 := by
  intro r q hr hq hne
  have hcop : r.Coprime q := (Nat.coprime_primes hr hq).2 hne
  have homega : ArithmeticFunction.cardDistinctFactors (r*q) = 2 := by
    rw [ArithmeticFunction.cardDistinctFactors_mul hcop,
        ArithmeticFunction.cardDistinctFactors_apply_prime hr,
        ArithmeticFunction.cardDistinctFactors_apply_prime hq]
  have hnot : ¬ IsPrimePow (r*q) := by
    intro hpp
    have h1 : ArithmeticFunction.cardDistinctFactors (r*q) = 1 :=
      ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr hpp
    omega
  have hv : ArithmeticFunction.vonMangoldt (r*q) = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := r*q)
  simp only [ArithmeticFunction.log_apply] at h
  rw [hv] at h
  simp only [neg_zero] at h
  have hR : (r*q).divisors.sum (fun d => -(ArithmeticFunction.moebius d : ℝ) * Real.log d)
      = -((r*q).divisors.sum (fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log d)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hR, h]
  ring
