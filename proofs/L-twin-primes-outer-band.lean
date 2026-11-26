import Mathlib

theorem PEqualNP.Outside.L_twin_primes_outer_band :
    let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ (x n : ℝ) (j : ℕ), 1000 ≤ x → x ≤ n → 50*n ≤ 51*x → 3 ≤ j → 9/4 < f x n j := by

  dsimp only
  intro x n j hx hxn hwin hj
  have hn : 0 < n := by linarith
  have hx0 : 0 < x := by linarith
  have hj3 : (3:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hmono : Real.log (1 + 3/n) ≤ Real.log (1 + (j:ℝ)/n) := by
    apply Real.log_le_log (by positivity)
    have hle : (3:ℝ)/n ≤ (j:ℝ)/n := div_le_div_of_nonneg_right hj3 (le_of_lt hn)
    linarith
  have hlog3 : 6/(2*n+3) ≤ Real.log (1 + 3/n) := by
    have h := Real.le_log_one_add_of_nonneg (x := 3/n) (by positivity)
    have he : (2:ℝ) * (3/n) / ((3/n) + 2) = 6/(2*n+3) := by
      field_simp
      ring
    rwa [he] at h
  have hstep : 6*x/(2*n+3) ≤ x * Real.log (1 + (j:ℝ)/n) := by
    have ha : 6*x/(2*n+3) = x * (6/(2*n+3)) := by ring
    rw [ha]
    exact le_trans (mul_le_mul_of_nonneg_left hlog3 (le_of_lt hx0))
      (mul_le_mul_of_nonneg_left hmono (le_of_lt hx0))
  have h4 : (9:ℝ)/4 < 6*x/(2*n+3) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*n + 3)]
    nlinarith
  linarith