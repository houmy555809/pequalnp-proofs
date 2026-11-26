import Mathlib

theorem PEqualNP.Outside.L_twin_primes_divisor_split :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let primes := fun X => (w X).filter Nat.Prime; let c := fun (d : ℕ) => -(ArithmeticFunction.moebius d : ℝ)*Real.log d; let short := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => d ≤ D)).sum c))/(X:ℝ); let long := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => D < d)).sum c))/(X:ℝ); ∀ X D : ℕ, short X D + long X D = (primes X).sum (fun p => Real.log p*ArithmeticFunction.vonMangoldt (p+2))/(X:ℝ) := by
  intro w' primes' c' short' long' X D
  have hmain : ∀ n : ℕ, (∑ d ∈ n.divisors, c' d) = ArithmeticFunction.vonMangoldt n := by
    intro n
    have h' : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d:ℝ))
        = -ArithmeticFunction.vonMangoldt n := by
      simpa using ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
    calc (∑ d ∈ n.divisors, c' d)
        = -(∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log (d:ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro d hd
          simp only [c', neg_mul]
      _ = -(-ArithmeticFunction.vonMangoldt n) := by rw [h']
      _ = ArithmeticFunction.vonMangoldt n := by simp
  simp only [short', long']
  rw [← add_div]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← mul_add]
  congr 1
  have hfilter : (p+2).divisors.filter (fun d => D < d)
      = (p+2).divisors.filter (fun d => ¬ d ≤ D) := by
    apply Finset.filter_congr
    intro d hd
    simp only [Nat.not_le]
  rw [hfilter, Finset.sum_filter_add_sum_filter_not (s := (p+2).divisors) (p := fun d => d ≤ D) (f := c')]
  exact hmain (p+2)
