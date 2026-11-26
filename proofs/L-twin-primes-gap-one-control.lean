import Mathlib

theorem PEqualNP.Outside.L_twin_primes_gap_one_control :
    ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+1) ≠ 0 → (∃ k : ℕ, n = 2^k) ∨ (∃ k : ℕ, n+1 = 2^k) := by

  intro n h
  rw [mul_ne_zero_iff] at h
  obtain ⟨hn, hn1⟩ := h
  rw [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hn hn1
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hn
  obtain ⟨q, l, hq, hl, hql⟩ := (isPrimePow_nat_iff (n+1)).mp hn1
  rcases Nat.even_or_odd n with he | ho
  · left
    have h2n : 2 ∣ n := even_iff_two_dvd.mp he
    have h2p : 2 ∣ p := by
      have hpk' : 2 ∣ p ^ k := by rw [hpk]; exact h2n
      exact Nat.prime_two.dvd_of_dvd_pow hpk'
    have hp2 : p = 2 := by
      rcases (Nat.dvd_prime hp).mp h2p with h1 | h1
      · exact absurd h1 (by norm_num)
      · exact h1.symm
    exact ⟨k, by rw [← hpk, hp2]⟩
  · right
    have h2n : 2 ∣ n + 1 := by
      obtain ⟨m, hm⟩ := ho
      exact ⟨m + 1, by omega⟩
    have h2q : 2 ∣ q := by
      have hql' : 2 ∣ q ^ l := by rw [hql]; exact h2n
      exact Nat.prime_two.dvd_of_dvd_pow hql'
    have hq2 : q = 2 := by
      rcases (Nat.dvd_prime hq).mp h2q with h1 | h1
      · exact absurd h1 (by norm_num)
      · exact h1.symm
    exact ⟨l, by rw [← hql, hq2]⟩