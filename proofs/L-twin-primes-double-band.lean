import Mathlib

theorem PEqualNP.Outside.L_twin_primes_double_band :
    let f := fun (x n j : ℝ) => x * Real.log (1+j/n); ∀ x n : ℝ, 1000 ≤ x → x ≤ n → 50*n ≤ 51*x → |f x n 2 - 2| < 1/20 := by

  dsimp only
  intro x n hx hxn hwin
  have hn : 0 < n := by linarith
  have hx0 : 0 < x := by linarith
  have hlog_lower : 2/(n+1) ≤ Real.log (1 + 2/n) := by
    have h := Real.le_log_one_add_of_nonneg (x := 2/n) (by positivity)
    have he : (2:ℝ) * (2/n) / ((2/n) + 2) = 2/(n+1) := by
      field_simp
      ring
    rwa [he] at h
  have hlog_upper : Real.log (1 + 2/n) ≤ 2/n := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 2/n by positivity)
    simpa using h
  have hlow : (39:ℝ)/20 < x * Real.log (1 + 2/n) := by
    have h1 : x * (2/(n+1)) ≤ x * Real.log (1 + 2/n) :=
      mul_le_mul_of_nonneg_left hlog_lower (le_of_lt hx0)
    have h2 : x * (2/(n+1)) = 2*x/(n+1) := by ring
    rw [h2] at h1
    have h3 : (39:ℝ)/20 < 2*x/(n+1) := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < n + 1)]
      nlinarith
    linarith
  have hup : x * Real.log (1 + 2/n) ≤ 2 := by
    have h1 : x * Real.log (1 + 2/n) ≤ x * (2/n) :=
      mul_le_mul_of_nonneg_left hlog_upper (le_of_lt hx0)
    have h2 : x * (2/n) = 2*x/n := by ring
    rw [h2] at h1
    have h3 : 2*x/n ≤ 2 := by
      rw [div_le_iff₀ hn]
      linarith
    linarith
  rw [abs_lt]
  constructor <;> linarith